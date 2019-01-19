// Copyright 2018 Mozilla

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::{cmp::Ordering,
          collections::{HashMap, HashSet},
          fmt,
          ops::Deref};

use error::{ErrorKind, Result};
use guid::{Guid, ROOT_GUID, UNFILED_GUID, USER_CONTENT_ROOTS};

/// The type for entry indices in the tree.
type Index = usize;

/// Describes where a new item's parent GUID comes from. A valid tree
/// should have matching GUIDs from both an item's parent's `children` and
/// an item's `parentid`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ParentGuidFrom(Option<Guid>, Option<Guid>);

impl Default for ParentGuidFrom {
    fn default() -> Self {
        ParentGuidFrom(None, None)
    }
}

impl ParentGuidFrom {
    /// Notes that the parent `guid` comes from an item's parent's `children`.
    pub fn children(self, guid: &Guid) -> ParentGuidFrom {
        ParentGuidFrom(Some(guid.to_owned()), self.1)
    }

    /// Notes that the parent `guid` comes from an item's `parentid`.
    pub fn item(self, guid: &Guid) -> ParentGuidFrom {
        ParentGuidFrom(self.0, Some(guid.to_owned()))
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum Child {
    Missing(Guid),
    Existing(Item),
}

impl Child {
    fn guid(&self) -> &Guid {
        match self {
            Child::Missing(guid) => guid,
            Child::Existing(item) => item.guid(),
        }
    }
}

impl From<Item> for Child {
    fn from(item: Item) -> Child {
        Child::Existing(item)
    }
}

/// A complete, rooted bookmark tree with tombstones.
///
/// The tree stores bookmark items in a vector, and uses indices in the vector
/// to identify parents and children. This makes traversal and lookup very
/// efficient for well-formed trees. Retrieving a node's parent takes one
/// indexing operation, retrieving children takes one indexing operation per
/// child, and retrieving a node by random GUID takes one hash map lookup and
/// one indexing operation.
///
/// We need to do more work to fix up trees with structure inconsistencies.
/// However, the cost should amortize well across merges.
///
/// # Tree structure
///
/// In a well-formed tree:
///
/// - Each item exists in exactly one folder. Two different folder's
///   `children` should never reference the same item.
/// - Each folder contains existing children. A folder's `children` should
///   never reference tombstones, or items that don't exist in the tree at all.
/// - Each item has a `parentid` that agrees with its parent's `children`. In
///   other words, if item B's `parentid` is A, then A's `children` should
///   contain B.
///
/// Because of Reasons, things are (a lot) messier in practice.
///
/// # Structure inconsistencies
///
/// Sync stores structure in two places: a `parentid` property on each item,
/// which points to its parent's GUID, and a list of ordered `children` on the
/// item's parent. They're duplicated because, historically, Sync clients didn't
/// stage incoming records. Instead, they applied records one at a time,
/// directly to the live local tree. This meant that, if a client saw a child
/// before its parent, it would first use the `parentid` to decide where to keep
/// the child, then fix up parents and positions using the parent's `children`.
///
/// This is also why moving an item into a different folder uploads records for
/// the item, old folder, and new folder. The item has a new `parentid`, and the
/// folders have new `children`. Similarly, deleting an item uploads a tombstone
/// for the item, and a record for the item's old parent.
///
/// Unfortunately, bugs (bug 1258127) and missing features (bug 1253051) in
/// older clients sometimes caused them to upload invalid or incomplete changes.
/// For example, a client might have:
///
/// - Uploaded a moved child, but not its parents. This means the child now
///   appears in multiple parents. In the most extreme case, an item might be
///   referenced in two different sets of `children`, _and_ have a third,
///   completely unrelated `parentid`.
/// - Deleted a child, and tracked the deletion, but didn't flag the parent for
///   reupload. The parent folder now has a tombstone child.
/// - Tracked and uploaded items that shouldn't exist on the server at all,
///   like the left pane or reading list roots (bug 1309255).
/// - Missed new folders created during a sync, creating holes in the tree.
///
/// Newer clients shouldn't do this, but we might still have inconsistent
/// records on the server that will confuse older clients. Additionally, Firefox
/// for iOS includes a much stricter bookmarks engine that refuses to sync if
/// it detects inconsistencies.
///
/// # Divergences
///
/// To work around this, our tree lets the structure _diverge_. This allows:
///
/// - Items with multiple parents.
/// - Items with missing `parentid`s.
/// - Folders with `children` whose `parentid`s don't match the folder.
/// - Items whose `parentid`s don't mention the item in their `children`.
/// - Items with `parentid`s that point to nonexistent or deleted folders.
/// - Folders with nonexistent `children`.
/// - Non-syncable items, like custom roots.
/// - Any combination of these.
///
/// Each item in the tree has an `EntryParentFrom` tag that indicates where
/// its structure comes from. Structure from `children` is validated and
/// resolved at `insert` time, so trying to add an item to a parent that
/// doesn't exist or isn't a folder returns a `MissingParent` or
/// `InvalidParent` error.
///
/// Structure from `parentid`, if it diverges from `children`, is resolved at
/// merge time, when the merger walks the complete tree. You can think of this
/// distinction as similar to early vs. late binding. The `parentid`, if
/// different from the parent's `children`, might not exist in the tree at
/// `insert` time, either because the parent hasn't been added yet, or because
/// it doesn't exist in the tree at all.
///
/// # Resolving divergences
///
/// Walking the tree, using `Tree::node_for_guid`, `Node::parent`, and
/// `Node::children`, resolves divergences using these rules:
///
/// 1. Items that appear in multiple `children`, and items with mismatched
///    `parentid`s, use the chronologically newer parent, based on the parent's
///    last modified time. We always prefer structure from `children` over
///    `parentid,` because `children` also gives us the item's position.
/// 2. Items that aren't mentioned in any parent's `children`, but have a
///    `parentid` that references an existing folder in the tree, are reparented
///    to the end of that folder, after the folder's `children`.
/// 3. Items that reference a nonexistent or non-folder `parentid`, or don't
///    have a `parentid` at all, are reparented to the default folder, after any
///    `children` and items from rule 2.
/// 4. If the default folder isn't set, or doesn't exist, items from rule 3 are
///    reparented to the root instead.
///
/// The result is a well-formed tree structure that can be merged. The merger
/// detects if the structure diverged, and flags affected items for reupload.
#[derive(Debug)]
pub struct Tree {
    entries: Vec<Entry>,
    entry_index_by_guid: HashMap<Guid, Index>,
    deleted_guids: HashSet<Guid>,
    orphan_indices_by_parent_guid: HashMap<Guid, Vec<Index>>,
    reparent_orphans_to: Option<Guid>,
}

impl Default for Tree {
    fn default() -> Self {
        Tree::with_reparenting(Item::Existing {
            guid: ROOT_GUID.clone(),
            parent_guid: None,
            kind: Kind::Folder,
            age: 0,
            needs_merge: false,
        }, &UNFILED_GUID)
    }
}

impl Tree {
    /// Constructs a new rooted tree.
    pub fn new(root: Item) -> Tree {
        let mut entry_index_by_guid = HashMap::new();
        entry_index_by_guid.insert(root.guid().clone(), 0);

        Tree {
            entries: vec![Entry::root(root)],
            entry_index_by_guid,
            deleted_guids: HashSet::new(),
            orphan_indices_by_parent_guid: HashMap::new(),
            reparent_orphans_to: None,
        }
    }

    pub fn with_reparenting(root: Item, reparent_orphans_to: &Guid) -> Tree {
        let mut entry_index_by_guid = HashMap::new();
        entry_index_by_guid.insert(root.guid().clone(), 0);

        Tree {
            entries: vec![Entry::root(root)],
            entry_index_by_guid,
            deleted_guids: HashSet::new(),
            orphan_indices_by_parent_guid: HashMap::new(),
            reparent_orphans_to: Some(reparent_orphans_to.to_owned()),
        }
    }

    #[inline]
    pub fn root(&self) -> Node {
        Node(self, &self.entries[0], Divergence::Ok)
    }

    pub fn deletions<'t>(&'t self) -> impl Iterator<Item = &Guid> + 't {
        self.deleted_guids.iter()
    }

    pub fn is_deleted(&self, guid: &Guid) -> bool {
        self.deleted_guids.contains(guid)
    }

    pub fn note_deleted(&mut self, guid: Guid) {
        self.deleted_guids.insert(guid);
    }

    pub fn guids<'t>(&'t self) -> impl Iterator<Item = &Guid> + 't {
        self.entry_index_by_guid
            .keys()
            .chain(self.deleted_guids.iter())
    }

    /// Returns the node for a given `guid`, or `None` if a node with the `guid`
    /// doesn't exist in the tree, or was deleted.
    pub fn node_for_guid(&self, guid: &Guid) -> Option<Node> {
        self.entry_index_by_guid.get(guid).map(|&index| {
            let entry = &self.entries[index];
            if self.orphan_indices_by_parent_guid.contains_key(entry.item.guid()) {
                // Check if this node has reparented orphans (rule 2).
                return Node(self, entry, Divergence::Diverged);
            }
            if entry.is(&self.entries[self.reparent_to_index()]) {
                // If this node is the default folder for reparented orphans,
                // check if we have any remaining orphans that reference
                // nonexistent or non-folder parents (rule 3).
                let needs_reparenting = |guid| {
                    match self.entry_index_by_guid.get(guid) {
                        Some(&index) => !self.entries[index].item.is_folder(),
                        None => true,
                    }
                };
                if self.orphan_indices_by_parent_guid.keys().any(needs_reparenting) {
                    return Node(self, entry, Divergence::Diverged);
                }
            }
            match &entry.parents {
                EntryParents::Root => {
                    Node(self, entry, entry.divergence)
                },
                EntryParents::One(parent_from) => match parent_from {
                    EntryParentFrom::Children(_) => {
                        Node(self, entry, entry.divergence)
                    },
                    EntryParentFrom::Item(_) => {
                        Node(self, entry, Divergence::Diverged)
                    }
                },
                EntryParents::Many(_) => Node(self, entry, Divergence::Diverged)
            }
        })
    }

    /// Adds a child to the tree, allowing for orphans and multiple parents.
    pub fn insert(&mut self, parent_guid: ParentGuidFrom, child: Child) -> Result<()> {
        let entry_index = self.entry_index(&child)?;
        let (divergence, parents) = self.structure_for(parent_guid, &child)?;
        match entry_index {
            // An entry for the item already exists in the tree, so we need to
            // mark the item, its existing parents, and new parents as diverged.
            EntryIndex::Existing(entry_index) => {
                // Add the entry to the new parents.
                for parent_index in parents.indices() {
                    let parent_entry = &mut self.entries[parent_index];
                    parent_entry.child_indices.push(entry_index);
                }
                for parent_guid in parents.guids() {
                    let child_indices = self.orphan_indices_by_parent_guid
                        .entry(parent_guid)
                        .or_default();
                    child_indices.push(entry_index);
                }

                // Update the existing entry's parents.
                let parent_indices = {
                    let mut entry = &mut self.entries[entry_index];
                    let new_parents = entry.parents.clone().diverge(parents)
                        .expect("Roots can't diverge");
                    if let Child::Existing(item) = child {
                        // Don't replace existing items with placeholders for
                        // missing children. This should be impossible on
                        // Desktop, which joins `items` and `structure` on the
                        // GUID, but we can't assert that statically.
                        entry.item = item;
                    }
                    entry.divergence = Divergence::Diverged;
                    entry.parents = new_parents;
                    entry.parents.indices()
                };

                // Flag all parents as diverged.
                for parent_index in parent_indices {
                    let parent_entry = &mut self.entries[parent_index];
                    parent_entry.divergence = Divergence::Diverged;
                }
            },

            // The item doesn't exist in the tree yet, so just add it.
            EntryIndex::New(entry_index) => match child {
                Child::Existing(item) => {
                    // Add the entry to the new parents.
                    for parent_index in parents.indices() {
                        let parent_entry = &mut self.entries[parent_index];
                        parent_entry.child_indices.push(entry_index);
                    }
                    for parent_guid in parents.guids() {
                        let child_indices = self.orphan_indices_by_parent_guid
                            .entry(parent_guid)
                            .or_default();
                        child_indices.push(entry_index);
                    }

                    self.entry_index_by_guid.insert(item.guid().to_owned(), entry_index);
                    self.entries.insert(entry_index, Entry {
                        item,
                        divergence,
                        parents,
                        child_indices: Vec::new(),
                    });
                },

                Child::Missing(_) => {
                    for parent_index in parents.indices() {
                        let parent_entry = &mut self.entries[parent_index];
                        parent_entry.divergence = Divergence::Diverged;
                    }
                },
            },
        };
        Ok(())
    }

    /// Returns the index of an entry for an item in the tree, or the index at
    /// which the item should be inserted if it doesn't exist in the tree.
    fn entry_index(&self, child: &Child) -> Result<EntryIndex> {
        match self.entry_index_by_guid.get(child.guid()) {
            Some(&entry_index) => {
                let entry = &self.entries[entry_index];
                if let EntryParents::Root = &entry.parents {
                    // Don't allow duplicate roots. `Tree::insert` panics if
                    // roots diverge.
                    return Err(ErrorKind::DuplicateItem(child.guid().to_owned()).into());
                }
                Ok(EntryIndex::Existing(entry_index))
            },
            None => Ok(EntryIndex::New(self.entries.len())),
        }
    }

    /// Determines the structure for a new or duplicate item.
    fn structure_for(&self, parent_guid: ParentGuidFrom, child: &Child)
                     -> Result<(Divergence, EntryParents)> {
        Ok(match parent_guid {
            ParentGuidFrom(None, from_item) => {
                // The item isn't mentioned in a folder's `children`, but may
                // have a `parentid`. Try the item's `parentid`, the default
                // folder for orphans, and the root, in order.
                let parent_from = from_item.map(|parent_guid| {
                    EntryParentFrom::Item(parent_guid)
                }).unwrap_or_else(|| {
                    match &self.reparent_orphans_to {
                        Some(parent_guid) => EntryParentFrom::Item(parent_guid.to_owned()),
                        None => EntryParentFrom::Children(0),
                    }
                });
                (Divergence::Diverged, EntryParents::One(parent_from))
            },
            ParentGuidFrom(Some(from_children), from_item) => {
                // The item is mentioned in at least one folder's `children`,
                // and may also have a `parentid`.
                let parent_index = match self.entry_index_by_guid.get(&from_children) {
                    Some(parent_index) => *parent_index,
                    None => return Err(ErrorKind::MissingParent(child.guid().to_owned(),
                                                                from_children.to_owned()).into()),
                };
                let parent_entry = &self.entries[parent_index];
                if !parent_entry.item.is_folder() {
                    return Err(ErrorKind::InvalidParent(child.guid().to_owned(),
                                                        parent_entry.item.guid().to_owned()).into());
                }
                from_item.map(|from_item| {
                    if from_item == from_children {
                        // If the parent's `children` and item's
                        // `parentid` agree, great!
                        (Divergence::Ok,
                         EntryParents::One(EntryParentFrom::Children(parent_index)))
                    } else {
                        (Divergence::Diverged, EntryParents::Many(vec![
                            EntryParentFrom::Children(parent_index),
                            EntryParentFrom::Item(from_item),
                        ]))
                    }
                }).unwrap_or_else(|| {
                    // If the item doesn't have a `parentid`, mark it as
                    // diverged so that the merger reuploads it.
                    (Divergence::Diverged,
                     EntryParents::One(EntryParentFrom::Children(parent_index)))
                })
            },
        })
    }

    fn reparent_to_index(&self) -> Index {
        self.reparent_orphans_to
            .as_ref()
            .and_then(|guid| self.entry_index_by_guid.get(guid))
            .cloned()
            .unwrap_or(0)
    }

    /// ...
    fn index_for_reparenting(&self, parent_guid: &Guid) -> Index {
        self.entry_index_by_guid.get(parent_guid)
            .cloned()
            .unwrap_or_else(|| self.reparent_to_index())
    }

    /// ...
    fn children_for_entry<'t>(&'t self, entry: &'t Entry) -> impl Iterator<Item = Node> + 't {
        let orphans = match self.orphan_indices_by_parent_guid.get(entry.item.guid()) {
            Some(child_indices) => child_indices.iter()
                .map(|&child_index| {
                    Node(self, &self.entries[child_index], Divergence::Diverged)
                })
                .collect(),
            None => Vec::new()
        };

        let reparented_orphans = if entry.is(&self.entries[self.reparent_to_index()]) {
            self.orphan_indices_by_parent_guid.iter()
                .filter(|(guid, _)| !self.entry_index_by_guid.contains_key(guid))
                .flat_map(|(_, child_indices)| {
                    child_indices.iter().map(|&child_index| {
                        Node(self, &self.entries[child_index], Divergence::Diverged)
                    })
                })
                .collect()
        } else {
            Vec::new()
        };

        entry.child_indices.iter().filter_map(move |&child_index| {
            let child_entry = &self.entries[child_index];
            self.parent_for_entry(child_entry).and_then(|parent_node| {
                if parent_node.entry().is(entry) {
                    Some(Node(self, child_entry, child_entry.divergence))
                } else {
                    None
                }
            })
        }).chain(orphans.into_iter()).chain(reparented_orphans.into_iter())
    }

    /// ...
    fn parent_for_entry(&self, entry: &Entry) -> Option<Node> {
        match &entry.parents {
            EntryParents::Root => None,
            EntryParents::One(parent_from) => {
                let parent_index = match parent_from {
                    EntryParentFrom::Children(parent_index) => *parent_index,
                    EntryParentFrom::Item(guid) => self.index_for_reparenting(guid),
                };
                let parent_entry = &self.entries[parent_index];
                Some(Node(self, parent_entry, parent_entry.divergence))
            },
            EntryParents::Many(parents_from) => {
                parents_from.iter().min_by(|a, b| {
                    let (parent_index, other_parent_index) = match (a, b) {
                        (EntryParentFrom::Children(_), EntryParentFrom::Item(_)) => {
                            return Ordering::Less;
                        },
                        (EntryParentFrom::Item(_), EntryParentFrom::Children(_)) => {
                            return Ordering::Greater;
                        },
                        (EntryParentFrom::Children(parent_index),
                            EntryParentFrom::Children(other_parent_index)) => {

                            (*parent_index, *other_parent_index)
                        },
                        (EntryParentFrom::Item(guid), EntryParentFrom::Item(other_guid)) => {
                            (self.index_for_reparenting(guid),
                             self.index_for_reparenting(other_guid))
                        },
                    };
                    let entry = &self.entries[parent_index];
                    let other_entry = &self.entries[other_parent_index];
                    entry.item.age().cmp(&other_entry.item.age())
                }).map(|parent_from| {
                    let parent_index = match parent_from {
                        EntryParentFrom::Children(parent_index) => *parent_index,
                        EntryParentFrom::Item(guid) => self.index_for_reparenting(guid),
                    };
                    let parent_entry = &self.entries[parent_index];
                    Node(self, parent_entry, Divergence::Diverged)
                })
            },
        }
    }
}

impl fmt::Display for Tree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let root = self.root();
        let deleted_guids = self.deleted_guids
                                .iter()
                                .map(|guid| guid.as_ref())
                                .collect::<Vec<&str>>();
        match deleted_guids.len() {
            0 => write!(f, "{}", root.to_ascii_string()),
            _ => {
                write!(f,
                       "{}\nDeleted: [{}]",
                       root.to_ascii_string(),
                       deleted_guids.join(","))
            },
        }
    }
}

#[cfg(test)]
impl PartialEq for Tree {
    fn eq(&self, other: &Tree) -> bool {
        if self.entry_index_by_guid.len() != other.entry_index_by_guid.len() {
            return false;
        }
        if self.orphan_indices_by_parent_guid.len() != other.orphan_indices_by_parent_guid.len() {
            return false;
        }
        for (guid, &index) in &self.entry_index_by_guid {
            let other_index = match other.entry_index_by_guid.get(guid) {
                Some(&other_index) => other_index,
                None => return false,
            };
            let entry = &self.entries[index];
            let other_entry = &other.entries[other_index];
            if entry.item != other_entry.item {
                return false;
            }
            let parents_match = match (&entry.parents, &other_entry.parents) {
                (EntryParents::Root, EntryParents::Root) => true,
                (EntryParents::One(parent), EntryParents::One(other_parent)) => {
                    match (parent, other_parent) {
                        (EntryParentFrom::Children(parent_index),
                            EntryParentFrom::Children(other_parent_index)) => {

                            let parent_entry = &self.entries[*parent_index];
                            let other_parent_entry = &self.entries[*other_parent_index];
                            parent_entry.item.guid() == other_parent_entry.item.guid()
                        },
                        (EntryParentFrom::Item(guid),
                            EntryParentFrom::Item(other_guid)) => guid == other_guid,
                        _ => false,
                    }
                },
                (EntryParents::Many(parents), EntryParents::Many(other_parents)) => {
                    if parents.len() == other_parents.len() {
                        parents.iter()
                            .zip(other_parents.iter())
                            .all(|(parent, other_parent)| {
                                match (parent, other_parent) {
                                    (EntryParentFrom::Children(parent_index),
                                        EntryParentFrom::Children(other_parent_index)) => {

                                        let parent_entry = &self.entries[*parent_index];
                                        let other_parent_entry = &self.entries[*other_parent_index];
                                        parent_entry.item.guid() == other_parent_entry.item.guid()
                                    },
                                    (EntryParentFrom::Item(guid),
                                        EntryParentFrom::Item(other_guid)) => guid == other_guid,
                                    _ => false,
                                }
                            })
                    } else {
                        false
                    }
                },
                _ => false,
            };
            if !parents_match {
                return false;
            }
            let children_match = if entry.child_indices.len() == other_entry.child_indices.len() {
                entry.child_indices.iter()
                    .zip(other_entry.child_indices.iter())
                    .all(|(&child_index, &other_child_index)| {
                        let child_entry = &self.entries[child_index];
                        let other_child_entry = &self.entries[other_child_index];
                        child_entry.item.guid() == other_child_entry.item.guid()
                    })
            } else {
                false
            };
            if !children_match {
                return false;
            }
        }
        for other_guid in other.entry_index_by_guid.keys() {
            if !self.entry_index_by_guid.contains_key(other_guid) {
                return false;
            }
        }
        true
    }
}

/// The index of an existing entry in the tree, or the index at which a new
/// entry should be inserted.
enum EntryIndex {
    New(Index),
    Existing(Index),
}

/// An entry wraps a tree item with references to its parents and children,
/// which index into the tree's `entries` vector. This indirection exists
/// because Rust is more strict about ownership of parents and children.
///
/// For example, we can't have entries own their children without sacrificing
/// fast random lookup: we'd need to store references to the entries in the
/// lookup map, but a struct can't hold references into itself.
///
/// Similarly, we can't have entries hold `Weak` pointers to `Rc` entries for
/// the parent and children, because we need to update the parent when we insert
/// a new node, but `Rc` won't hand us a mutable reference to the entry as long
/// as it has outstanding `Weak` pointers.
///
/// We *could* use GUIDs instead of indices, and store the entries in a
/// `HashMap<String, Entry>`, but that's inefficient: we'd need to store N
/// copies of the GUID for parent and child lookups, and retrieving children
/// would take one hash map lookup *per child*.
#[derive(Debug)]
struct Entry {
    item: Item,
    divergence: Divergence,
    parents: EntryParents,
    child_indices: Vec<Index>,
}

impl Entry {
    fn root(root: Item) -> Entry {
        Entry {
            item: root.into(),
            divergence: Divergence::Ok,
            parents: EntryParents::Root,
            child_indices: Vec::new(),
        }
    }

    fn is(&self, other: &Entry) -> bool {
        self as *const _ == other as *const _
    }
}

/// Stores structure state for an entry.
#[derive(Clone, Debug)]
enum EntryParents {
    /// The entry is a top-level root, from which all other entries descend.
    /// A tree can only have one root.
    Root,

    /// The entry has exactly one parent. This is the case for records with
    /// `parentid`s that match their parents' `children`, and orphans with
    /// a `parentid` that aren't mentioned in any parents' `children`.
    One(EntryParentFrom),

    /// The entry has multiple parents. This is the case where an item appears
    /// in multiple parents, or where the item's `parentid` doesn't match its
    /// parent's `children`.
    Many(Vec<EntryParentFrom>),
}

impl EntryParents {
    fn diverge(self, parents: EntryParents) -> Option<EntryParents> {
        match (self, parents) {
            (EntryParents::Root, EntryParents::Root) => Some(EntryParents::Root),
            (EntryParents::One(old_parent), EntryParents::One(new_parent)) => {
                Some(EntryParents::Many(vec![old_parent, new_parent]))
            },
            (EntryParents::One(old_parent), EntryParents::Many(mut new_parents)) => {
                new_parents.push(old_parent);
                Some(EntryParents::Many(new_parents))
            },
            (EntryParents::Many(mut old_parents), EntryParents::One(new_parent)) => {
                old_parents.push(new_parent);
                Some(EntryParents::Many(old_parents))
            },
            (EntryParents::Many(old_parents), EntryParents::Many(mut new_parents)) => {
                new_parents.extend(old_parents);
                Some(EntryParents::Many(new_parents))
            },
            _ => None,
        }
    }

    fn indices(&self) -> Vec<Index> {
        match self {
            EntryParents::Root => Vec::new(),
            EntryParents::One(parent_from) => match parent_from {
                EntryParentFrom::Children(parent_index) => vec![*parent_index],
                EntryParentFrom::Item(_) => Vec::new(),
            },
            EntryParents::Many(parents_from) => {
                parents_from.iter().filter_map(|parent_from| match parent_from {
                    EntryParentFrom::Children(index) => Some(*index),
                    EntryParentFrom::Item(_) => None,
                }).collect()
            }
        }
    }

    fn guids(&self) -> Vec<Guid> {
        match self {
            EntryParents::Root => Vec::new(),
            EntryParents::One(parent_from) => match parent_from {
                EntryParentFrom::Children(_) => Vec::new(),
                EntryParentFrom::Item(guid) => vec![guid.to_owned()],
            },
            EntryParents::Many(parents_from) => {
                parents_from.iter().filter_map(|parent_from| match parent_from {
                    EntryParentFrom::Children(_) => None,
                    EntryParentFrom::Item(guid) => Some(guid.to_owned()),
                }).collect()
            }
        }
    }
}


/// Describes where an entry's parent comes from.
///
/// `EntryParentFrom` notes inconsistencies like orphans, multiple parents,
/// and parent-child disagreements, which the `Merger` uses to resolve invalid
/// structure and produce a consistent tree.
#[derive(Clone, Debug)]
enum EntryParentFrom {
    /// The entry's parent references the entry in its `children`, meaning we
    /// know the index of the parent.
    Children(Index),

    /// The entry's parent comes from its `parentid`. We can only store the
    /// GUID and not the index because the tree might not have an entry for the
    /// `parentid` yet.
    Item(Guid),
}

#[derive(Clone, Copy, Debug)]
enum Divergence {
    /// The node's structure is already correct, and doesn't need to be
    /// reuploaded.
    Ok,

    /// The node exists in multiple parents, or is a reparented orphan.
    /// The merger should reupload the node.
    Diverged,
}

/// A convenience wrapper around `Entry` that dereferences to the containing
/// item, and follows indices for parents and children.
#[derive(Clone, Copy, Debug)]
pub struct Node<'t>(&'t Tree, &'t Entry, Divergence);

impl<'t> Node<'t> {
    #[inline]
    fn tree(&self) -> &'t Tree { &self.0 }

    #[inline]
    fn entry(&self) -> &'t Entry { &self.1 }

    pub fn children<'n>(&'n self) -> impl Iterator<Item = Node<'t>> + 'n {
        self.tree().children_for_entry(self.entry())
    }

    pub fn parent(&self) -> Option<Node> {
        self.tree().parent_for_entry(self.entry())
    }

    pub fn level(&self) -> Option<i64> {
        if self.entry().item.guid() == &ROOT_GUID {
            return Some(0);
        }
        self.tree().parent_for_entry(self.entry())
            .and_then(|parent| parent.level())
            .map(|level| level + 1)
    }

    /// Syncable items descend from the four user content roots. Any
    /// other roots and their descendants, like the left pane root,
    /// left pane queries, and custom roots, are non-syncable.
    ///
    /// Newer Desktops should never reupload non-syncable items
    /// (bug 1274496), and should have removed them in Places
    /// migrations (bug 1310295). However, these items may be
    /// reparented locally to the unfiled root, in which case they're seen as
    /// syncable. If the remote tree has the missing parents
    /// and roots, we'll determine that the items are non-syncable
    /// when merging, remove them locally, and mark them for deletion
    /// remotely.
    pub fn is_syncable(&self) -> bool {
        if self.entry().item.guid() == &ROOT_GUID {
            return false;
        }
        if USER_CONTENT_ROOTS.contains(self.entry().item.guid()) {
            return true;
        }
        self.tree().parent_for_entry(self.entry())
            .map(|parent| parent.is_syncable())
            .unwrap_or(false)
    }

    pub fn diverged(&self) -> bool {
        match &self.2 {
            Divergence::Ok => false,
            Divergence::Diverged => true,
        }
    }

    pub fn to_ascii_string(&self) -> String {
        self.to_ascii_fragment("")
    }

    fn to_ascii_fragment(&self, prefix: &str) -> String {
        match &self.entry().item {
            Item::Missing(guid) => format!("{}❓ {}", prefix, guid),
            Item::Existing { kind, .. } => match kind {
                Kind::Folder => {
                    match &self.entry().child_indices.len() {
                        0 => format!("{}📂 {}", prefix, &self.entry().item),
                        _ => {
                            let children_prefix = format!("{}| ", prefix);
                            let children = self.children()
                                            .map(|n| n.to_ascii_fragment(&children_prefix))
                                            .collect::<Vec<String>>()
                                            .join("\n");
                            format!("{}📂 {}\n{}", prefix, &self.entry().item, children)
                        },
                    }
                },
                _ => format!("{}🔖 {}", prefix, &self.entry().item),
            }
        }
    }
}

impl<'t> Deref for Node<'t> {
    type Target = Item;

    fn deref(&self) -> &Item {
        &self.entry().item
    }
}

impl<'t> fmt::Display for Node<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.entry().item.fmt(f)
    }
}

/// An item in a local or remote bookmark tree.
#[derive(Debug, Eq, PartialEq)]
pub enum Item {
    Missing(Guid),
    Existing {
        guid: Guid,
        parent_guid: Option<Guid>,
        kind: Kind,
        age: i64,
        needs_merge: bool,
    },
}

impl Item {
    #[inline]
    pub fn guid(&self) -> &Guid {
        match self {
            Item::Missing(guid) => guid,
            Item::Existing { guid, .. } => guid
        }
    }

    #[inline]
    pub fn needs_merge(&self) -> bool {
        match self {
            Item::Missing(_) => false,
            Item::Existing { needs_merge, .. } => *needs_merge
        }
    }

    #[inline]
    pub fn age(&self) -> i64 {
        match self {
            Item::Missing(_) => 0,
            Item::Existing { age, .. } => *age,
        }
    }

    #[inline]
    pub fn is_folder(&self) -> bool {
        match self {
            Item::Missing(_) => false,
            Item::Existing { kind, .. } => kind == &Kind::Folder
        }
    }

    pub fn has_compatible_kind(&self, remote_node: &Item) -> bool {
        match (self, remote_node) {
            (Item::Missing(_), _) => false,
            (_, Item::Missing(_)) => false,
            (Item::Existing { kind, .. }, Item::Existing { kind: other_kind, .. }) => {
                match (&kind, &other_kind) {
                    // Bookmarks and queries are interchangeable, as simply changing the URL
                    // can cause it to flip kinds.
                    (Kind::Bookmark, Kind::Query) => true,
                    (Kind::Query, Kind::Bookmark) => true,
                    (local_kind, remote_kind) => local_kind == remote_kind,
                }
            }
        }
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Item::Missing(guid) => write!(f, "{} (Missing)", guid),
            Item::Existing { needs_merge, guid, kind, age, .. } => {
                let info = if *needs_merge {
                    format!("{}; Age = {}ms; Unmerged", kind, age)
                } else {
                    format!("{}; Age = {}ms", kind, age)
                };
                write!(f, "{} ({})", guid, info)
            }
        }
    }
}

/// Synced item kinds. Each corresponds to a Sync record type.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Kind {
    Bookmark,
    Query,
    Folder,
    Livemark,
    Separator,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// A merged bookmark node that indicates which side to prefer, and holds merged
/// child nodes.
#[derive(Debug)]
pub struct MergedNode<'t> {
    pub guid: Guid,
    pub merge_state: MergeState<'t>,
    pub merged_children: Vec<MergedNode<'t>>,
}

impl<'t> MergedNode<'t> {
    pub fn new(guid: Guid, merge_state: MergeState<'t>) -> MergedNode<'t> {
        MergedNode { guid,
                     merge_state,
                     merged_children: Vec::new(), }
    }

    /// Indicates whether to prefer the remote side when applying the merged tree.
    pub fn use_remote(&self) -> bool {
        match self.merge_state {
            MergeState::Remote { .. } | MergeState::RemoteWithNewStructure { .. } => true,
            _ => false,
        }
    }

    /// Indicates whether the merged item should be (re)uploaded to the server.
    pub fn needs_upload(&self) -> bool {
        match self.merge_state {
            MergeState::Local(_)
            | MergeState::LocalWithNewStructure(_)
            | MergeState::RemoteWithNewStructure(_) => true,
            _ => false,
        }
    }

    #[cfg(test)]
    pub fn into_tree(self) -> Result<Tree> {
        fn to_item<'t>(parent_guid: Option<Guid>, merged_node: &MergedNode<'t>) -> Item {
            match &*merged_node.node() {
                Item::Missing(guid) => Item::Missing(guid.clone()),
                Item::Existing { kind, age, .. } => Item::Existing {
                    guid: merged_node.guid.clone(),
                    parent_guid,
                    kind: *kind,
                    age: *age,
                    needs_merge: match merged_node.merge_state {
                        MergeState::Local(_)
                        | MergeState::Remote(_)
                        | MergeState::Unchanged { .. } => false,
                        _ => true,
                    },
                },
            }
        }

        fn inflate<'t>(tree: &mut Tree,
                    parent_guid: &Guid,
                    merged_node: MergedNode<'t>)
                    -> Result<()>
        {
            let guid = merged_node.guid.clone();
            tree.insert(ParentGuidFrom::default()
                            .children(parent_guid)
                            .item(parent_guid),
                        to_item(Some(parent_guid.clone()), &merged_node).into())?;
            for merged_child_node in merged_node.merged_children {
                inflate(tree, &guid, merged_child_node)?;
            }
            Ok(())
        }

        let guid = self.guid.clone();
        let mut tree = Tree::new(to_item(None, &self));
        for merged_child_node in self.merged_children {
            inflate(&mut tree, &guid, merged_child_node)?;
        }
        Ok(tree)
    }

    pub fn to_ascii_string(&self) -> String {
        self.to_ascii_fragment("")
    }

    fn to_ascii_fragment(&self, prefix: &str) -> String {
        match &*self.node() {
            Item::Missing(guid) => format!("{}❓ {}", prefix, guid),
            Item::Existing { kind, ..} => match kind {
                Kind::Folder => match self.merged_children.len() {
                    0 => format!("{}📂 {}", prefix, &self),
                    _ => {
                        let children_prefix = format!("{}| ", prefix);
                        let children = self.merged_children
                                        .iter()
                                        .map(|n| n.to_ascii_fragment(&children_prefix))
                                        .collect::<Vec<String>>()
                                        .join("\n");
                        format!("{}📂 {}\n{}", prefix, &self, children)
                    },
                },
                _ => format!("{}🔖 {}", prefix, &self),
            }
        }
    }

    fn node(&self) -> Node {
        match self.merge_state {
            MergeState::Local(node) => node,
            MergeState::Remote(node) => node,
            MergeState::LocalWithNewStructure(node) => node,
            MergeState::RemoteWithNewStructure(node) => node,
            MergeState::Unchanged { local_node, .. } => local_node,
        }
    }
}

impl<'t> fmt::Display for MergedNode<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.guid, self.merge_state)
    }
}

/// The merge state indicates which node we should prefer, local or remote, when
/// resolving conflicts.
#[derive(Clone, Copy, Debug)]
pub enum MergeState<'t> {
    /// A local merge state means no changes: we keep the local value and
    /// structure state. This could mean that the item doesn't exist on the
    /// server yet, or that it has newer local changes that we should
    /// upload.
    Local(Node<'t>),

    /// A remote merge state means we should update the local value and
    /// structure state. The item might not exist locally yet, or might have
    /// newer remote changes that we should apply.
    Remote(Node<'t>),

    /// A local merge state with new structure means we should prefer the local
    /// value state, and upload the new structure state to the server. We use
    /// new structure states to resolve conflicts caused by moving local items
    /// out of a remotely deleted folder, or remote items out of a locally
    /// deleted folder.
    LocalWithNewStructure(Node<'t>),

    /// A remote merge state with new structure means we should prefer the
    /// remote value and reupload the new structure.
    RemoteWithNewStructure(Node<'t>),

    /// An unchanged merge state means we don't need to do anything to the item.
    Unchanged { local_node: Node<'t>, remote_node: Node<'t> },
}

impl<'t> MergeState<'t> {
    pub fn with_new_structure(&self) -> MergeState<'t> {
        match *self {
            MergeState::Local(node) => {
                MergeState::LocalWithNewStructure(node)
            },
            MergeState::Remote(node) => {
                MergeState::RemoteWithNewStructure(node)
            },
            MergeState::Unchanged { local_node, .. } => {
                // Once the structure changes, it doesn't matter which side we
                // pick; we'll need to reupload the item to the server, anyway.
                MergeState::LocalWithNewStructure(local_node)
            },
            state => state,
        }
    }
}

impl<'t> fmt::Display for MergeState<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            MergeState::Local(_) => "(Local, Local)",
            MergeState::Remote(_) => "(Remote, Remote)",
            MergeState::LocalWithNewStructure(_) => "(Local, New)",
            MergeState::RemoteWithNewStructure(_) => "(Remote, New)",
            MergeState::Unchanged { .. } => "(Unchanged, Unchanged)"
        })
    }
}

/// Content info for an item in the local or remote tree. This is used to dedupe
/// new local items to remote items that don't exist locally, with different
/// GUIDs and similar content.
///
/// - Bookmarks must have the same title and URL.
/// - Queries must have the same title and query URL.
/// - Folders and livemarks must have the same title.
/// - Separators must have the same position within their parents.
#[derive(Debug, Eq, Hash, PartialEq)]
pub enum Content {
    Bookmark { title: String, url_href: String },
    Folder { title: String },
    Separator { position: i64 },
}

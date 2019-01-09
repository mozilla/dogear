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

use std::{collections::{HashMap, HashSet},
          fmt,
          ops::Deref};

use error::{ErrorKind, Result};
use guid::{Guid, ROOT_GUID, USER_CONTENT_ROOTS};

/// A complete, rooted bookmark tree with tombstones.
///
/// The tree stores bookmark nodes in a vector, and uses indices in the vector
/// to identify parents and children. This makes traversal and lookup very
/// efficient. Retrieving a node's parent takes one indexing operation,
/// retrieving children takes one indexing operation per child, and retrieving a
/// node by random GUID takes one hash map lookup and one indexing operation.
#[derive(Debug)]
pub struct Tree {
    entries: Vec<Entry>,
    index_by_guid: HashMap<Guid, usize>,
    deleted_guids: HashSet<Guid>,
}

impl Default for Tree {
    fn default() -> Self {
        Tree::new(Item::Existing {
            guid: ROOT_GUID.clone(),
            parent_guid: None,
            kind: Kind::Folder,
            age: 0,
            needs_merge: false,
        })
    }
}

impl Tree {
    /// Constructs a new rooted tree.
    pub fn new(root: Item) -> Tree {
        let mut index_by_guid = HashMap::new();
        index_by_guid.insert(root.guid().clone(), 0);

        let entries = vec![Entry { parent_index: None,
                                   item: root,
                                   level: 0,
                                   is_syncable: false,
                                   child_indices: Vec::new(), }];

        Tree { entries,
               index_by_guid,
               deleted_guids: HashSet::new(), }
    }

    #[inline]
    pub fn root(&self) -> Node {
        self.node(0)
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
        self.index_by_guid
            .keys()
            .chain(self.deleted_guids.iter())
    }

    pub fn node_for_guid(&self, guid: &Guid) -> Option<Node> {
        self.index_by_guid
            .get(guid)
            .map(|index| self.node(*index))
    }

    pub fn insert(&mut self, parent_guid: &Guid, item: Item) -> Result<()> {
        if self.index_by_guid.contains_key(item.guid()) {
            return Err(ErrorKind::DuplicateItem(item.guid().clone()).into());
        }
        let child_index = self.entries.len();
        let (parent_index, level, is_syncable) = match self.index_by_guid.get(&parent_guid) {
            Some(parent_index) => {
                let parent = &mut self.entries[*parent_index];
                if !parent.item.is_folder() {
                    return Err(ErrorKind::InvalidParent(item.guid().clone(),
                                                        parent.item.guid().clone()).into());
                }
                parent.child_indices.push(child_index);

                // Syncable items descend from the four user content roots. Any
                // other roots and their descendants, like the left pane root,
                // left pane queries, and custom roots, are non-syncable.
                //
                // Newer Desktops should never reupload non-syncable items
                // (bug 1274496), and should have removed them in Places
                // migrations (bug 1310295). However, these items may be
                // orphaned in the unfiled root, in which case they're seen as
                // syncable locally. If the remote tree has the missing parents
                // and roots, we'll determine that the items are non-syncable
                // when merging, remove them locally, and mark them for deletion
                // remotely.
                let is_syncable = USER_CONTENT_ROOTS.contains(item.guid()) || parent.is_syncable;

                (*parent_index, parent.level + 1, is_syncable)
            },
            None => return Err(ErrorKind::MissingParent(item.guid().clone(),
                                                        parent_guid.clone()).into()),
        };
        self.index_by_guid.insert(item.guid().clone(), child_index);
        self.entries.push(Entry { parent_index: Some(parent_index),
                                  item,
                                  level,
                                  is_syncable,
                                  child_indices: Vec::new(), });
        Ok(())
    }

    fn node(&self, index: usize) -> Node {
        Node(self, &self.entries[index])
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
        if self.index_by_guid.len() != other.index_by_guid.len() {
            return false;
        }
        for (guid, index) in &self.index_by_guid {
            if let Some(other_index) = other.index_by_guid.get(guid) {
                let entry = &self.entries[*index];
                let other_entry = &other.entries[*other_index];
                if entry.item != other_entry.item {
                    return false;
                }
                match (entry.parent_index, other_entry.parent_index) {
                    (Some(parent_index), Some(other_parent_index)) => {
                        let parent_guid = &self.entries[parent_index].item.guid();
                        let other_parent_guid = &other.entries[other_parent_index].item.guid();
                        if parent_guid != other_parent_guid {
                            return false;
                        }
                    },
                    (None, None) => {},
                    _ => return false,
                };
                let child_guids = entry.child_indices
                                       .iter()
                                       .map(|index| self.entries[*index].item.guid());
                let other_child_guids =
                    other_entry.child_indices
                               .iter()
                               .map(|other_index| other.entries[*other_index].item.guid());
                if child_guids.ne(other_child_guids) {
                    return false;
                }
            } else {
                return false;
            }
        }
        for other_guid in other.index_by_guid.keys() {
            if !self.index_by_guid.contains_key(other_guid) {
                return false;
            }
        }
        true
    }
}

/// An entry wraps a tree item with references to its parent and children, which
/// index into the tree's `entries` vector. This indirection exists because
/// Rust is more strict about ownership of parents and children.
///
/// For example, we can't have entries own their children without sacrificing
/// fast random lookup, because we'd need to store references to the entries
/// in the lookup map, but a struct can't hold references into itself.
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
    parent_index: Option<usize>,
    item: Item,
    level: i64,
    is_syncable: bool,
    child_indices: Vec<usize>,
}

/// A convenience wrapper around `Entry` that dereferences to the containing
/// item, and follows indices for parents and children.
#[derive(Clone, Copy, Debug)]
pub struct Node<'t>(&'t Tree, &'t Entry);

impl<'t> Node<'t> {
    pub fn children<'n>(&'n self) -> impl Iterator<Item = Node<'t>> + 'n {
        self.1
            .child_indices
            .iter()
            .map(move |index| self.0.node(*index))
    }

    pub fn parent(&self) -> Option<Node<'t>> {
        self.1
            .parent_index
            .as_ref()
            .map(|index| self.0.node(*index))
    }

    #[inline]
    pub fn level(&self) -> i64 {
        self.1.level
    }

    #[inline]
    pub fn is_syncable(&self) -> bool {
        self.1.is_syncable
    }

    pub fn to_ascii_string(&self) -> String {
        self.to_ascii_fragment("")
    }

    fn to_ascii_fragment(&self, prefix: &str) -> String {
        match &self.1.item {
            Item::Missing(guid) => format!("{}❓ {}", prefix, guid),
            Item::Existing { kind, .. } => match kind {
                Kind::Folder => {
                    match self.1.child_indices.len() {
                        0 => format!("{}📂 {}", prefix, &self.1.item),
                        _ => {
                            let children_prefix = format!("{}| ", prefix);
                            let children = self.children()
                                            .map(|n| n.to_ascii_fragment(&children_prefix))
                                            .collect::<Vec<String>>()
                                            .join("\n");
                            format!("{}📂 {}\n{}", prefix, &self.1.item, children)
                        },
                    }
                },
                _ => format!("{}🔖 {}", prefix, &self.1.item),
            }
        }
    }
}

impl<'t> Deref for Node<'t> {
    type Target = Item;

    fn deref(&self) -> &Item {
        &self.1.item
    }
}

impl<'t> fmt::Display for Node<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.1.item.fmt(f)
    }
}

/// An item in a local or remote bookmark tree.
#[derive(Clone, Debug, Eq, PartialEq)]
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
            tree.insert(&parent_guid, to_item(Some(parent_guid.clone()), &merged_node))?;
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

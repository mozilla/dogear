/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{cmp::{Eq, PartialEq},
          collections::{HashMap, HashSet},
          fmt,
          ops::Deref};

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
    index_by_guid: HashMap<String, usize>,
    deleted_guids: HashSet<String>,
}

impl Tree {
    /// Constructs a new rooted tree.
    pub fn new(root: Item) -> Tree {
        let mut index_by_guid = HashMap::new();
        index_by_guid.insert(root.guid.to_string(), 0);
        Tree { entries: vec![Entry { parent_index: None,
                                     item: root,
                                     level: 0,
                                     child_indices: Vec::new(), }],
               index_by_guid,
               deleted_guids: HashSet::new(), }
    }

    pub fn deletions<'t>(&'t self) -> impl Iterator<Item = &str> + 't {
        self.deleted_guids.iter().map(move |guid| guid.as_ref())
    }

    pub fn is_deleted(&self, guid: &str) -> bool {
        self.deleted_guids.contains(guid)
    }

    pub fn note_deleted<T>(&mut self, guid: T)
        where T: Into<String> {
        self.deleted_guids.insert(guid.into());
    }

    pub fn guids<'t>(&'t self) -> impl Iterator<Item = &str> + 't {
        self.index_by_guid
            .keys()
            .chain(self.deleted_guids.iter())
            .map(move |guid| guid.as_ref())
    }

    pub fn node_for_guid<T>(&self, guid: T) -> Option<Node>
        where T: AsRef<str> {
        self.index_by_guid
            .get(guid.as_ref())
            .map(|index| self.node(*index))
    }

    pub fn insert<T>(&mut self, parent_guid: T, item: Item)
        where T: AsRef<str> {
        assert!(!self.index_by_guid.contains_key(&item.guid),
                "Entry {} already exists in tree",
                &item.guid);
        let child_index = self.entries.len();
        let (parent_index, level) = match self.index_by_guid.get(parent_guid.as_ref()) {
            Some(parent_index) => {
                let parent = &mut self.entries[*parent_index];
                assert!(parent.item.is_folder(),
                        "Can't insert {} into non-folder {}",
                        &item.guid,
                        &parent.item.guid);
                parent.child_indices.push(child_index);
                (*parent_index, parent.level + 1)
            },
            None => panic!("Missing parent {} for {}", &item.guid, parent_guid.as_ref()),
        };
        self.index_by_guid
            .insert(item.guid.to_string(), child_index);
        self.entries.push(Entry { parent_index: Some(parent_index),
                                  item,
                                  level,
                                  child_indices: Vec::new(), });
    }

    fn node(&self, index: usize) -> Node {
        Node(self, &self.entries[index])
    }
}

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
                        let parent_guid = &self.entries[parent_index].item.guid;
                        let other_parent_guid = &other.entries[other_parent_index].item.guid;
                        if parent_guid != other_parent_guid {
                            return false;
                        }
                    },
                    (None, None) => {},
                    _ => return false,
                };
                let child_guids = entry.child_indices
                                       .iter()
                                       .map(|index| &self.entries[*index].item.guid);
                let other_child_guids =
                    other_entry.child_indices
                               .iter()
                               .map(|other_index| &other.entries[*other_index].item.guid);
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

impl Eq for Tree {}

impl<'t> From<MergedNode<'t>> for Tree {
    fn from(root: MergedNode<'t>) -> Self {
        fn to_item<'t>(node: &MergedNode<'t>) -> Item {
            let value_state = node.merge_state.value();
            let decided_value = value_state.node();
            let mut item = Item::new(&node.guid, decided_value.kind);
            item.age = decided_value.age;
            item
        }

        fn inflate<'t>(tree: &mut Tree, parent_guid: &str, node: MergedNode<'t>) {
            let guid = node.guid.clone();
            tree.insert(parent_guid, to_item(&node));
            node.merged_children
                .into_iter()
                .for_each(|merged_child_node| inflate(tree, &guid, merged_child_node));
        }

        let guid = root.guid.clone();
        let mut tree = Tree::new(to_item(&root));
        root.merged_children
            .into_iter()
            .for_each(|merged_child_node| inflate(&mut tree, &guid, merged_child_node));
        tree
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
    level: u64,
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

    pub fn level(&self) -> u64 {
        self.1.level
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
#[derive(Debug, Eq, PartialEq)]
pub struct Item {
    pub guid: String,
    pub age: i64,
    pub kind: Kind,
    pub needs_merge: bool,
    pub is_syncable: bool,
}

impl Item {
    pub fn new(guid: &str, kind: Kind) -> Item {
        Item { guid: guid.to_string(),
               kind,
               age: 0,
               needs_merge: false,
               is_syncable: true, }
    }

    #[inline]
    pub fn is_folder(&self) -> bool {
        self.kind == Kind::Folder
    }

    #[inline]
    pub fn newer_than(&self, other: &Item) -> bool {
        self.age < other.age
    }

    pub fn has_compatible_kind(&self, remote_node: &Item) -> bool {
        match (&self.kind, &remote_node.kind) {
            // Bookmarks and queries are interchangeable, as simply changing the URL
            // can cause it to flip kinds.
            (Kind::Bookmark, Kind::Query) => true,
            (Kind::Query, Kind::Bookmark) => true,

            // A local folder can become a livemark, as the remote may have synced
            // as a folder before the annotation was added. However, we don't allow
            // a local livemark to "downgrade" to a folder. See bug 632287.
            (Kind::Folder, Kind::Livemark) => true,
            (local_kind, remote_kind) => local_kind == remote_kind,
        }
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let info = if self.needs_merge {
            format!("({}; Age = {}ms; Unmerged", self.kind, self.age)
        } else {
            format!("({}; Age = {}ms", self.kind, self.age)
        };
        write!(f, "{} ({})", self.guid, info)
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
    pub guid: String,
    pub merge_state: MergeState<'t>,
    pub merged_children: Vec<MergedNode<'t>>,
}

impl<'t> MergedNode<'t> {
    pub fn new(guid: String, merge_state: MergeState<'t>) -> MergedNode<'t> {
        MergedNode { guid,
                     merge_state,
                     merged_children: Vec::new(), }
    }
}

impl<'t> fmt::Display for MergedNode<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.guid, self.merge_state)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ValueState<'t> {
    Local(Node<'t>),
    Remote(Node<'t>),
}

impl<'t> ValueState<'t> {
    pub fn node(&self) -> &Node<'t> {
        match self {
            ValueState::Local(node) => node,
            ValueState::Remote(node) => node,
        }
    }
}

impl<'t> fmt::Display for ValueState<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
                        ValueState::Local(_) => "Value: Local",
                        ValueState::Remote(_) => "Value: Remote",
                    })
    }
}

#[derive(Clone, Copy, Debug)]
pub enum StructureState {
    Local,
    Remote,
    New,
}

impl fmt::Display for StructureState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
                        StructureState::Local => "Structure: Local",
                        StructureState::Remote => "Structure: Remote",
                        StructureState::New => "Structure: New",
                    })
    }
}

/// The merge state indicates which node we should prefer, local or remote, when
/// resolving conflicts.
#[derive(Clone, Copy, Debug)]
pub struct MergeState<'t>(ValueState<'t>, StructureState);

impl<'t> MergeState<'t> {
    /// A local merge state means no changes: we keep the local value and
    /// structure state. This could mean that the item doesn't exist on the
    /// server yet, or that it has newer local changes that we should
    /// upload.
    pub fn local(node: Node<'t>) -> MergeState<'t> {
        MergeState(ValueState::Local(node), StructureState::Local)
    }

    /// A remote merge state means we should update the local value and
    /// structure state. The item might not exist locally yet, or might have
    /// newer remote changes that we should apply.
    pub fn remote(node: Node<'t>) -> MergeState<'t> {
        MergeState(ValueState::Remote(node), StructureState::Remote)
    }

    /// Takes an existing value state, and a new structure state. We use the new
    /// merge state to resolve conflicts caused by moving local items out of a
    /// remotely deleted folder, or remote items out of a locally deleted
    /// folder.
    ///
    /// New merged nodes should be reuploaded to the server.
    pub fn new(old: MergeState<'t>) -> MergeState<'t> {
        MergeState(old.0, StructureState::New)
    }

    #[inline]
    pub fn value(&self) -> ValueState {
        self.0
    }

    #[inline]
    pub fn structure(&self) -> StructureState {
        self.1
    }
}

impl<'t> fmt::Display for MergeState<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}; {}", self.0, self.1)
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

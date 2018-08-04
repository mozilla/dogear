/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{cmp::{Eq, PartialEq},
          collections::HashSet,
          fmt,
          hash::{Hash, Hasher},
          iter};

/// Synced item kinds. Each corresponds to a Sync record type.
#[derive(Eq, Hash, PartialEq)]
pub enum Kind {
    Bookmark,
    Query,
    Folder,
    Livemark,
    Separator,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
                        Kind::Bookmark => "Bookmark",
                        Kind::Query => "Query",
                        Kind::Folder => "Folder",
                        Kind::Livemark => "Livemark",
                        Kind::Separator => "Separator",
                    })
    }
}

/// A complete, rooted tree with tombstones.
pub struct Tree {
    pub deleted_guids: HashSet<String>,
}

impl Tree {
    pub fn is_deleted(&self, guid: &str) -> bool {
        false
    }

    pub fn node_for_guid(&self, guid: &str) -> Option<&Node> {
        None
    }

    pub fn parent_node_for(&self, child_node: &Node) -> &Node {
        unimplemented!();
    }

    pub fn guids(&self) -> impl Iterator<Item = &str> {
        iter::empty::<&str>()
    }
}

/// A node in a local or remote bookmark tree.
pub struct Node {
    pub guid: String,
    pub age: u64,
    pub kind: Kind,
    pub needs_merge: bool,
    pub level: u64,
    pub is_syncable: bool,
    pub children: Vec<Box<Node>>,
}

impl Node {
    #[inline]
    pub fn is_folder(&self) -> bool {
        self.kind == Kind::Folder
    }

    #[inline]
    pub fn newer_than(&self, other: &Node) -> bool {
        self.age < other.age
    }

    pub fn has_compatible_kind(&self, remote_node: &Node) -> bool {
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

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let info = if self.needs_merge {
            format!("({}; Age = {}ms; Unmerged", self.kind, self.age)
        } else {
            format!("({}; Age = {}ms", self.kind, self.age)
        };
        write!(f, "{} ({})", self.guid, info)
    }
}

/// A node in a merged bookmark tree. Holds the local node, remote node,
/// merged children, and a merge state indicating which side to prefer.
pub struct MergedNode<'t> {
    pub guid: String,
    pub local_node: Option<&'t Node>,
    pub remote_node: Option<&'t Node>,
    pub merge_state: MergeState,
    pub merged_children: Vec<Box<MergedNode<'t>>>,
}

impl<'t> MergedNode<'t> {
    pub fn new(guid: String,
               local_node: Option<&'t Node>,
               remote_node: Option<&'t Node>,
               merge_state: MergeState)
               -> MergedNode<'t>
    {
        MergedNode { guid,
                     local_node,
                     remote_node,
                     merge_state,
                     merged_children: Vec::new(), }
    }
}

impl<'t> fmt::Display for MergedNode<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.guid, self.merge_state)
    }
}

#[derive(Clone)]
pub enum ValueState {
    Local,
    Remote,
}

impl fmt::Display for ValueState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
                        ValueState::Local => "Value: Local",
                        ValueState::Remote => "Value: Remote",
                    })
    }
}

#[derive(Clone)]
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

/// The merge state indicates which node we should prefer when reconciling
/// with Places. Recall that a merged node may point to a local node, remote
/// node, or both.
#[derive(Clone)]
pub struct MergeState(ValueState, StructureState);

impl MergeState {
    /// A local merge state means no changes: we keep the local value and
    /// structure state. This could mean that the item doesn't exist on the
    /// server yet, or that it has newer local changes that we should
    /// upload.
    ///
    /// It's an error for a merged node to have a local merge state without a
    /// local node. Deciding the value state for the merged node asserts
    /// this.
    pub fn local() -> MergeState {
        MergeState(ValueState::Local, StructureState::Local)
    }

    /// A remote merge state means we should update Places with new value and
    /// structure state from the mirror. The item might not exist locally yet,
    /// or might have newer remote changes that we should apply.
    ///
    /// As with local, a merged node can't have a remote merge state without a
    /// remote node.
    pub fn remote() -> MergeState {
        MergeState(ValueState::Remote, StructureState::Remote)
    }

    /// Takes an existing value state, and a new structure state. We use the new
    /// merge state to resolve conflicts caused by moving local items out of a
    /// remotely deleted folder, or remote items out of a locally deleted
    /// folder.
    ///
    /// Applying a new merged node bumps its local change counter, so that the
    /// merged structure is reuploaded to the server.
    pub fn new(old: MergeState) -> MergeState {
        MergeState(old.0, StructureState::New)
    }
}

impl fmt::Display for MergeState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}; {}", self.0, self.1)
    }
}

/// Content info for an item in the local or remote tree. This is used to dedupe
/// NEW local items to remote items that don't exist locally.
pub struct Content {
    pub title: String,
    pub url_href: String,
    pub position: i64,
}

/// A lookup key for a node and its content. This is used to match nodes with
/// different GUIDs and similar content.
///
/// - Bookmarks must have the same title and URL.
/// - Queries must have the same title and query URL.
/// - Folders and livemarks must have the same title.
/// - Separators must have the same position within their parents.
pub struct ContentDupeKey<'t>(&'t Node, &'t Content);

impl<'t> ContentDupeKey<'t> {
    pub fn new(node: &'t Node, content: &'t Content) -> ContentDupeKey<'t> {
        ContentDupeKey(node, content)
    }
}

impl<'t> PartialEq for ContentDupeKey<'t> {
    fn eq(&self, other: &ContentDupeKey) -> bool {
        if self.0.kind != other.0.kind {
            false
        } else {
            match self.0.kind {
                Kind::Bookmark | Kind::Query => {
                    self.1.title == other.1.title && self.1.url_href == other.1.url_href
                },
                Kind::Folder | Kind::Livemark => self.1.title == other.1.title,
                Kind::Separator => self.1.position == other.1.position,
            }
        }
    }
}

impl<'t> Eq for ContentDupeKey<'t> {}

impl<'t> Hash for ContentDupeKey<'t> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.kind.hash(state);
        match self.0.kind {
            Kind::Bookmark | Kind::Query => {
                self.1.title.hash(state);
                self.1.url_href.hash(state);
            },
            Kind::Folder | Kind::Livemark => {
                self.1.title.hash(state);
            },
            Kind::Separator => {
                self.1.position.hash(state);
            },
        }
    }
}

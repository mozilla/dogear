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

use std::{collections::{HashMap, HashSet, VecDeque},
          mem};

use error::{ErrorKind, Result};
use guid::{Guid, USER_CONTENT_ROOTS};
use tree::{Content, MergeState, MergedNode, Node, Tree};

/// Structure change types, used to indicate if a node on one side is moved
/// or deleted on the other.
#[derive(Eq, PartialEq)]
enum StructureChange {
    /// Node not deleted, or doesn't exist, on the other side.
    Unchanged,
    /// Node moved on the other side.
    Moved,
    /// Node deleted on the other side.
    Deleted,
}

#[derive(Clone, Copy, Default, Debug, Eq, PartialEq)]
pub struct StructureCounts {
    /// Remote non-folder change wins over local deletion.
    pub remote_revives: u64,
    /// Local folder deletion wins over remote change.
    pub local_deletes: u64,
    /// Local non-folder change wins over remote deletion.
    pub local_revives: u64,
    /// Remote folder deletion wins over local change.
    pub remote_deletes: u64,
    /// Deduped local items.
    pub dupes: u64,
}

/// Holds (matching remote dupes for local GUIDs, matching local dupes for
/// remote GUIDs).
type MatchingDupes<'t> = (HashMap<Guid, Node<'t>>, HashMap<Guid, Node<'t>>);

/// Represents an accepted local or remote deletion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Deletion {
    pub guid: Guid,
    pub local_level: i64,
    pub should_upload_tombstone: bool,
}

/// A two-way merger that produces a complete merged tree from a complete local
/// tree and a complete remote tree with changes since the last sync.
///
/// This is ported almost directly from iOS. On iOS, the `ThreeWayMerger` takes
/// a complete "mirror" tree with the server state after the last sync, and two
/// incomplete trees with local and remote changes to the mirror: "local" and
/// "mirror", respectively. Overlaying buffer onto mirror yields the current
/// server tree; overlaying local onto mirror yields the complete local tree.
///
/// Dogear doesn't store the shared parent for changed items, so we can only
/// do two-way merges. Our local tree is the union of iOS's mirror and local,
/// and our remote tree is the union of iOS's mirror and buffer.
///
/// Unlike iOS, Dogear doesn't distinguish between structure and value changes.
/// The `needs_merge` flag notes *that* a bookmark changed, but not *how*. This
/// means we might detect conflicts, and revert changes on one side, for cases
/// that iOS can merge cleanly.
///
/// Fortunately, most of our users don't organize their bookmarks into deeply
/// nested hierarchies, or make conflicting changes on multiple devices
/// simultaneously. A simpler two-way tree merge strikes a good balance between
/// correctness and complexity.
#[derive(Debug)]
pub struct Merger<'t> {
    local_tree: &'t Tree,
    new_local_contents: Option<&'t HashMap<Guid, Content>>,
    remote_tree: &'t Tree,
    new_remote_contents: Option<&'t HashMap<Guid, Content>>,
    matching_dupes_by_local_parent_guid: HashMap<Guid, MatchingDupes<'t>>,
    merged_guids: HashSet<Guid>,
    delete_locally: HashSet<Guid>,
    delete_remotely: HashSet<Guid>,
    structure_counts: StructureCounts,
}

impl<'t> Merger<'t> {
    pub fn new(local_tree: &'t Tree, remote_tree: &'t Tree) -> Merger<'t> {
        Merger { local_tree,
                 new_local_contents: None,
                 remote_tree,
                 new_remote_contents: None,
                 matching_dupes_by_local_parent_guid: HashMap::new(),
                 merged_guids: HashSet::new(),
                 delete_locally: HashSet::new(),
                 delete_remotely: HashSet::new(),
                 structure_counts: StructureCounts::default(), }
    }

    pub fn with_contents(local_tree: &'t Tree,
                         new_local_contents: &'t HashMap<Guid, Content>,
                         remote_tree: &'t Tree,
                         new_remote_contents: &'t HashMap<Guid, Content>)
                         -> Merger<'t>
    {
        Merger { local_tree,
                 new_local_contents: Some(new_local_contents),
                 remote_tree,
                 new_remote_contents: Some(new_remote_contents),
                 matching_dupes_by_local_parent_guid: HashMap::new(),
                 merged_guids: HashSet::new(),
                 delete_locally: HashSet::new(),
                 delete_remotely: HashSet::new(),
                 structure_counts: StructureCounts::default(), }
    }

    pub fn merge(&mut self) -> Result<MergedNode<'t>> {
        let merged_root_node = {
            let local_root_node = self.local_tree.root();
            let remote_root_node = self.remote_tree.root();
            self.two_way_merge(local_root_node, remote_root_node)?
        };

        // Any remaining deletions on one side should be deleted on the other side.
        // This happens when the remote tree has tombstones for items that don't
        // exist locally, or the local tree has tombstones for items that
        // aren't on the server.
        for guid in self.local_tree.deletions() {
            if !self.mentions(guid) {
                self.delete_remotely.insert(guid.clone());
            }
        }
        for guid in self.remote_tree.deletions() {
            if !self.mentions(guid) {
                self.delete_locally.insert(guid.clone());
            }
        }

        Ok(merged_root_node)
    }

    #[inline]
    pub fn telemetry(&self) -> &StructureCounts {
        &self.structure_counts
    }

    #[inline]
    pub fn subsumes(&self, tree: &Tree) -> bool {
        tree.guids().all(|guid| self.mentions(guid))
    }

    #[inline]
    pub fn deletions<'m>(&'m self) -> impl Iterator<Item = Deletion> + 'm {
        self.local_deletions().chain(self.remote_deletions())
    }

    fn local_deletions<'m>(&'m self) -> impl Iterator<Item = Deletion> + 'm {
        self.delete_locally.iter().filter_map(move |guid| {
            if self.delete_remotely.contains(guid) {
                None
            } else {
                let local_level = self.local_tree
                                      .node_for_guid(guid)
                                      .map(|node| node.level())
                                      .unwrap_or(-1);
                // Items that should be deleted locally already have tombstones
                // on the server, so we don't need to upload tombstones for
                // these deletions.
                Some(Deletion { guid: guid.clone(),
                                local_level,
                                should_upload_tombstone: false, })
            }
        })
    }

    fn remote_deletions<'m>(&'m self) -> impl Iterator<Item = Deletion> + 'm {
        self.delete_remotely.iter().map(move |guid| {
            let local_level = self.local_tree
                                  .node_for_guid(guid)
                                  .map(|node| node.level())
                                  .unwrap_or(-1);
            Deletion { guid: guid.to_owned(),
                       local_level,
                       should_upload_tombstone: true, }
        })
    }

    #[inline]
    fn mentions(&self, guid: &Guid) -> bool {
        self.merged_guids.contains(guid) ||
        self.delete_locally.contains(guid) ||
        self.delete_remotely.contains(guid)
    }

    fn merge_local_node(&mut self, local_node: Node<'t>) -> Result<MergedNode<'t>> {
        trace!("Item {} only exists locally", local_node);

        self.merged_guids.insert(local_node.guid.clone());

        let mut merged_node = MergedNode::new(local_node.guid.clone(),
                                              MergeState::local(local_node));
        if local_node.is_folder() {
            // The local folder doesn't exist remotely, but its children might, so
            // we still need to recursively walk and merge them. This method will
            // change the merge state from local to new if any children were moved
            // or deleted.
            for local_child_node in local_node.children() {
                self.merge_local_child_into_merged_node(&mut merged_node,
                                                        local_node,
                                                        None,
                                                        local_child_node)?;
            }
        }
        Ok(merged_node)
    }

    fn merge_remote_node(&mut self, remote_node: Node<'t>) -> Result<MergedNode<'t>> {
        trace!("Item {} only exists remotely", remote_node);

        self.merged_guids.insert(remote_node.guid.clone());

        let mut merged_node = MergedNode::new(remote_node.guid.clone(),
                                              MergeState::remote(remote_node));
        if remote_node.is_folder() {
            // As above, a remote folder's children might still exist locally, so we
            // need to merge them and update the merge state from remote to new if
            // any children were moved or deleted.
            for remote_child_node in remote_node.children() {
                self.merge_remote_child_into_merged_node(&mut merged_node,
                                                         None,
                                                         remote_node,
                                                         remote_child_node)?;
            }
        }
        Ok(merged_node)
    }

    /// Merges two nodes that exist locally and remotely.
    fn two_way_merge(&mut self,
                     local_node: Node<'t>,
                     remote_node: Node<'t>)
                     -> Result<MergedNode<'t>>
    {
        trace!("Item exists locally as {} and remotely as {}",
               local_node,
               remote_node);

        if !local_node.has_compatible_kind(&remote_node) {
            error!("Merging local {} and remote {} with different kinds",
                   local_node, remote_node);
            return Err(ErrorKind::MismatchedItemKind(local_node.kind, remote_node.kind).into());
        }

        self.merged_guids.insert(remote_node.guid.clone());

        if local_node.guid != remote_node.guid {
            // We deduped a NEW local item to a remote item.
            self.merged_guids.insert(local_node.guid.clone());
        }

        let mut merged_node = if USER_CONTENT_ROOTS.contains(&remote_node.guid) {
            // Don't update root titles or other properties.
            MergedNode::new(remote_node.guid.clone(),
                            MergeState::Local { local_node, remote_node: Some(remote_node) })
        } else {
            match (local_node.needs_merge, remote_node.needs_merge) {
                (true, true) => {
                    // The item changed locally and remotely. Use the timestamp
                    // to decide which is newer.
                    if local_node.newer_than(&remote_node) {
                        MergedNode::new(remote_node.guid.clone(),
                                        MergeState::Local { local_node, remote_node: Some(remote_node) })
                    } else {
                        MergedNode::new(remote_node.guid.clone(),
                                        MergeState::Remote { local_node: Some(local_node), remote_node })
                    }
                },
                (true, false) => {
                    // The item changed locally, but not remotely. Keep the
                    // local state.
                    MergedNode::new(remote_node.guid.clone(),
                                    MergeState::Local { local_node, remote_node: Some(remote_node) })
                },
                (false, true) => {
                    // The item changed remotely, but not locally. Take the
                    // remote state.
                    MergedNode::new(remote_node.guid.clone(),
                                    MergeState::Remote { local_node: Some(local_node), remote_node })
                },
                (false, false) => {
                  // The item is unchanged on both sides. Keep the local state.
                    MergedNode::new(remote_node.guid.clone(),
                                    MergeState::Local { local_node, remote_node: Some(remote_node) })
                },
            }
        };

        if local_node.newer_than(&remote_node) {
            // The folder exists locally and remotely, and the local node is newer.
            // Walk and merge local children first, followed by remaining unmerged
            // remote children.
            for local_child_node in local_node.children() {
                self.merge_local_child_into_merged_node(&mut merged_node,
                                                        local_node,
                                                        Some(remote_node),
                                                        local_child_node)?;
            }
            for remote_child_node in remote_node.children() {
                self.merge_remote_child_into_merged_node(&mut merged_node,
                                                         Some(local_node),
                                                         remote_node,
                                                         remote_child_node)?;
            }
            return Ok(merged_node);
        }

        // The folder exists locally and remotely, and the remote node is newer.
        // Merge remote children first, then remaining local children.
        for remote_child_node in remote_node.children() {
            self.merge_remote_child_into_merged_node(&mut merged_node,
                                                     Some(local_node),
                                                     remote_node,
                                                     remote_child_node)?;
        }
        for local_child_node in local_node.children() {
            self.merge_local_child_into_merged_node(&mut merged_node,
                                                    local_node,
                                                    Some(remote_node),
                                                    local_child_node)?;
        }
        Ok(merged_node)
    }

    /// Merges a remote child node into a merged folder node. This handles the
    /// following cases:
    ///
    /// - The remote child is locally deleted. We recursively move all of its
    ///   descendants that don't exist locally to the merged folder.
    /// - The remote child doesn't exist locally, but has a content match in the
    ///   corresponding local folder. We dedupe the local child to the remote
    ///   child.
    /// - The remote child exists locally, but in a different folder. We compare
    ///   merge flags and timestamps to decide where to keep the child.
    /// - The remote child exists locally, and in the same folder. We merge the
    ///   local and remote children.
    ///
    /// This is the inverse of `merge_local_child_into_merged_node`.
    ///
    /// Returns `true` if the merged structure state changed because the remote
    /// child was locally moved or deleted; `false` otherwise.
    fn merge_remote_child_into_merged_node(&mut self,
                                           merged_node: &mut MergedNode<'t>,
                                           local_parent_node: Option<Node<'t>>,
                                           remote_parent_node: Node<'t>,
                                           remote_child_node: Node<'t>)
                                           -> Result<()>
    {
        if self.merged_guids.contains(&remote_child_node.guid) {
            trace!("Remote child {} already seen in another folder and merged",
                   remote_child_node);
            return Ok(());
        }

        trace!("Merging remote child {} of {} into {}",
               remote_child_node,
               remote_parent_node,
               merged_node);

        // Check if the remote child is locally deleted. and move all
        // descendants that aren't also remotely deleted to the merged node.
        // This handles the case where a user deletes a folder on this device,
        // and adds a bookmark to the same folder on another device. We want to
        // keep the folder deleted, but we also don't want to lose the new
        // bookmark, so we move the bookmark to the deleted folder's parent.
        if self.check_for_local_structure_change_of_remote_node(merged_node,
                                                                remote_parent_node,
                                                                remote_child_node)? ==
           StructureChange::Deleted
        {
            // Flag the merged parent for reupload, since we deleted the
            // remote child.
            merged_node.merge_state = merged_node.merge_state.with_new_structure();
            return Ok(());
        }

        // The remote child isn't locally deleted. Does it exist in the local tree?
        if let Some(local_child_node) = self.local_tree.node_for_guid(&remote_child_node.guid) {
            // Otherwise, the remote child exists in the local tree. Did it move?
            let local_parent_node =
                local_child_node.parent()
                                .expect("Can't merge existing remote child without local parent");

            return self.merge_remote_child_node_with_local_child_node(merged_node,
                                                                      local_parent_node,
                                                                      local_child_node,
                                                                      remote_parent_node,
                                                                      remote_child_node);
        }

        // Remote child is not a root, and doesn't exist locally. Try to find a
        // content match in the containing folder, and dedupe the local item if
        // we can.
        trace!("Remote child {} doesn't exist locally; looking for local content match",
               remote_child_node);

        let merged_child_node = if let Some(local_child_node_by_content) =
            self.find_local_node_matching_remote_node(merged_node,
                                                      local_parent_node,
                                                      remote_parent_node,
                                                      remote_child_node)
        {
            self.two_way_merge(local_child_node_by_content, remote_child_node)
        } else {
            self.merge_remote_node(remote_child_node)
        }?;
        merged_node.merged_children.push(merged_child_node);
        Ok(())
    }

    /// Merges a local child node into a merged folder node.
    ///
    /// This is the inverse of `merge_remote_child_into_merged_node`.
    ///
    /// Returns `true` if the merged structure state changed because the local
    /// child doesn't exist remotely or was locally moved; `false` otherwise.
    fn merge_local_child_into_merged_node(&mut self,
                                          merged_node: &mut MergedNode<'t>,
                                          local_parent_node: Node<'t>,
                                          remote_parent_node: Option<Node<'t>>,
                                          local_child_node: Node<'t>)
                                          -> Result<()>
    {
        if self.merged_guids.contains(&local_child_node.guid) {
            // We already merged the child when we walked another folder.
            trace!("Local child {} already seen in another folder and merged",
                   local_child_node);
            return Ok(());
        }

        trace!("Merging local child {} of {} into {}",
               local_child_node,
               local_parent_node,
               merged_node);

        // Check if the local child is remotely deleted, and move any new local
        // descendants to the merged node if so.
        if self.check_for_remote_structure_change_of_local_node(merged_node,
                                                                local_parent_node,
                                                                local_child_node)? ==
           StructureChange::Deleted
        {
            // Since we're merging local nodes, we don't need to flag the merged
            // parent for reupload.
            return Ok(());
        }

        // At this point, we know the local child isn't deleted. See if it
        // exists in the remote tree.
        if let Some(remote_child_node) = self.remote_tree.node_for_guid(&local_child_node.guid) {
            // The local child exists remotely. It must have moved; otherwise, we
            // would have seen it when we walked the remote children.
            let remote_parent_node =
                remote_child_node.parent()
                                 .expect("Can't merge existing local child without remote parent");
            return self.merge_local_child_node_with_remote_child_node(merged_node,
                                                                      local_parent_node,
                                                                      local_child_node,
                                                                      remote_parent_node,
                                                                      remote_child_node);
        }

        // Local child is not a root, and doesn't exist remotely. Try to find a
        // content match in the containing folder, and dedupe the local item if
        // we can.
        trace!("Local child {} doesn't exist remotely; looking for remote content match",
               local_child_node);

        if let Some(remote_child_node_by_content) =
            self.find_remote_node_matching_local_node(merged_node,
                                                      local_parent_node,
                                                      remote_parent_node,
                                                      local_child_node)
        {
            // The local child has a remote content match, so take the remote GUID
            // and merge.
            let merged_child_node = self.two_way_merge(local_child_node,
                                                       remote_child_node_by_content)?;
            merged_node.merged_children.push(merged_child_node);
            return Ok(());
        }

        // The local child doesn't exist remotely, so flag the merged parent and
        // new child for upload, and walk its descendants.
        let mut merged_child_node = self.merge_local_node(local_child_node)?;
        merged_node.merge_state = merged_node.merge_state.with_new_structure();
        merged_child_node.merge_state = merged_child_node.merge_state.with_new_structure();
        merged_node.merged_children.push(merged_child_node);
        Ok(())
    }

    fn merge_local_child_node_with_remote_child_node(&mut self,
                                                     merged_node: &mut MergedNode<'t>,
                                                     local_parent_node: Node<'t>,
                                                     local_child_node: Node<'t>,
                                                     remote_parent_node: Node<'t>,
                                                     remote_child_node: Node<'t>)
                                                     -> Result<()>
    {
        trace!("Local child {} exists locally in {} and remotely in {}",
               local_child_node,
               local_parent_node,
               remote_parent_node);

        if self.local_tree.is_deleted(&remote_parent_node.guid) {
            trace!("Unconditionally taking local move for {} to {} because remote parent {} is \
                    deleted locally",
                   local_child_node,
                   local_parent_node,
                   remote_parent_node);

            // Merge and flag the new parent *and the locally moved child* for
            // reupload. The parent references the child in its `children`; the
            // child points back to the parent in its `parentid`.
            //
            // Reuploading the child isn't necessary for newer Desktops, which
            // ignore the child's `parentid` and use the parent's `children`.
            //
            // However, older Desktop and Android use the child's `parentid` as
            // canonical, while iOS is stricter and requires both to match.
            let mut merged_child_node = self.two_way_merge(local_child_node, remote_child_node)?;
            merged_node.merge_state = merged_node.merge_state.with_new_structure();
            merged_child_node.merge_state = merged_child_node.merge_state.with_new_structure();
            merged_node.merged_children.push(merged_child_node);
            return Ok(());
        }

        match (local_parent_node.needs_merge, remote_parent_node.needs_merge) {
            (true, true) => {
                // If both parents changed, compare timestamps to decide where
                // to keep the local child.
                let latest_local_age = local_child_node.age.min(local_parent_node.age);
                let latest_remote_age = remote_child_node.age.min(remote_parent_node.age);

                // Did the child move to a different folder?
                if local_parent_node.guid != remote_parent_node.guid {
                    if latest_remote_age <= latest_local_age {
                        // The remote move is newer, so we ignore the local
                        // move. We'll merge the local child later, when we
                        // walk its new remote parent.
                        trace!("Local child {} reparented locally to {} at {} and remotely to {} \
                                at {}; keeping child in newer remote parent",
                               local_child_node,
                               local_parent_node,
                               latest_local_age,
                               remote_parent_node,
                               latest_remote_age);

                        return Ok(());
                    }

                    // Otherwise, the local move is newer, so we merge the local
                    // child now and ignore the remote move.
                    trace!("Local child {} reparented locally to {} at {} and remotely to {} at \
                            {}; keeping child in newer local parent",
                           local_child_node,
                           local_parent_node,
                           latest_local_age,
                           remote_parent_node,
                           latest_remote_age);

                    // Merge and flag both the new parent and child for
                    // reupload. See above for why.
                    let mut merged_child_node = self.two_way_merge(local_child_node,
                                                                   remote_child_node)?;
                    merged_node.merge_state = merged_node.merge_state.with_new_structure();
                    merged_child_node.merge_state =
                        merged_child_node.merge_state.with_new_structure();
                    merged_node.merged_children.push(merged_child_node);
                    return Ok(());
                }

                // Otherwise, the child was repositioned in the same folder.
                // Compare timestamps to decide the child's new position.
                if latest_remote_age <= latest_local_age {
                    trace!("Local child {} repositioned locally in {} at {} and remotely in {} \
                            at {}; keeping child in newer remote position",
                           local_child_node,
                           local_parent_node,
                           latest_local_age,
                           remote_parent_node,
                           latest_remote_age);
                    return Ok(());
                }

                trace!("Local child {} repositioned locally in {} at {} and remotely in {} at \
                        {}; keeping child in newer local position",
                       local_child_node,
                       local_parent_node,
                       latest_local_age,
                       remote_parent_node,
                       latest_remote_age);

                // For position changes in the same folder, we only need to
                // merge and flag the parent for reupload.
                let merged_child_node = self.two_way_merge(local_child_node,
                                                           remote_child_node)?;
                merged_node.merge_state = merged_node.merge_state.with_new_structure();
                merged_node.merged_children.push(merged_child_node);
                Ok(())
            },

            (true, false) => {
                // If only the local parent changed, keep the local child in its
                // new parent.
                if local_parent_node.guid != remote_parent_node.guid {
                    trace!("Local child {} reparented locally to {}",
                           local_child_node,
                           local_parent_node);

                    // Merge and flag both the new parent and child for
                    // reupload.
                    let mut merged_child_node = self.two_way_merge(local_child_node,
                                                                   remote_child_node)?;
                    merged_node.merge_state = merged_node.merge_state.with_new_structure();
                    merged_child_node.merge_state =
                        merged_child_node.merge_state.with_new_structure();
                    merged_node.merged_children.push(merged_child_node);
                    return Ok(());
                }

                // Otherwise, the child was repositioned locally.
                trace!("Local child {} repositioned locally in {}",
                       local_child_node,
                       local_parent_node);

                // Only flag the parent of the repositioned local child for
                // reupload.
                let merged_child_node = self.two_way_merge(local_child_node,
                                                           remote_child_node)?;
                merged_node.merge_state = merged_node.merge_state.with_new_structure();
                merged_node.merged_children.push(merged_child_node);
                Ok(())
            },

            (false, _) => {
                trace!("Local child {} unchanged locally; keeping child in remote parent {}",
                       local_child_node,
                       remote_parent_node);
                Ok(())
            },
        }
    }

    fn merge_remote_child_node_with_local_child_node(&mut self,
                                                     merged_node: &mut MergedNode<'t>,
                                                     local_parent_node: Node<'t>,
                                                     local_child_node: Node<'t>,
                                                     remote_parent_node: Node<'t>,
                                                     remote_child_node: Node<'t>)
                                                     -> Result<()>
    {
        trace!("Remote child {} exists locally in {} and remotely in {}",
               remote_child_node,
               local_parent_node,
               remote_parent_node);

        if self.remote_tree.is_deleted(&local_parent_node.guid) {
            trace!("Unconditionally taking remote move for {} to {} because local parent {} is \
                    deleted remotely",
                   remote_child_node,
                   remote_parent_node,
                   local_parent_node);

            let merged_child_node = self.two_way_merge(local_child_node, remote_child_node)?;
            merged_node.merged_children.push(merged_child_node);

            return Ok(());
        }

        match (local_parent_node.needs_merge, remote_parent_node.needs_merge) {
            (true, true) => {
                // If both parents changed, compare timestamps to decide where
                // to keep the remote child.
                let latest_local_age = local_child_node.age.min(local_parent_node.age);
                let latest_remote_age = remote_child_node.age.min(remote_parent_node.age);

                if latest_remote_age > latest_local_age {
                    // The local move is newer, so we ignore the remote move.
                    // We'll merge the remote child later, when we walk its new
                    // local parent. Note that, since we only flag the remote
                    // parent here, we don't need to handle reparenting and
                    // repositioning separately.
                    trace!("Remote child {} moved locally to {} at {} and remotely to {} at {}; \
                            keeping child in newer local parent and position",
                           remote_child_node,
                           local_parent_node,
                           latest_local_age,
                           remote_parent_node,
                           latest_remote_age);

                    // Flag the old parent for reupload, since we're moving the
                    // remote child.
                    merged_node.merge_state = merged_node.merge_state.with_new_structure();
                    return Ok(());
                }

                // Otherwise, the remote move is newer, so we merge the remote
                // child now and ignore the local move.
                trace!("Remote child {} moved locally to {} at {} and remotely to {} at {}; \
                        keeping child in newer remote parent and position",
                       remote_child_node,
                       local_parent_node,
                       latest_local_age,
                       remote_parent_node,
                       latest_remote_age);

                let merged_child_node = self.two_way_merge(local_child_node,
                                                           remote_child_node)?;
                merged_node.merged_children.push(merged_child_node);
                Ok(())
            },

            (true, false) => {
                trace!("Remote child {} moved locally to {}",
                       remote_child_node,
                       local_parent_node);

                // Only flag the parent of the remote child for reupload.
                merged_node.merge_state = merged_node.merge_state.with_new_structure();
                Ok(())
            },

            (false, _) => {
                trace!("Remote child {} unchanged locally; keeping child in remote parent {}",
                       remote_child_node,
                       remote_parent_node);

                let merged_child_node = self.two_way_merge(local_child_node,
                                                           remote_child_node)?;
                merged_node.merged_children.push(merged_child_node);
                Ok(())
            },
        }
    }

    /// Checks if a remote node is locally moved or deleted, and reparents any
    /// descendants that aren't also remotely deleted to the merged node.
    ///
    /// This is the inverse of
    /// `check_for_remote_structure_change_of_local_node`.
    fn check_for_local_structure_change_of_remote_node(&mut self,
                                                       merged_node: &mut MergedNode<'t>,
                                                       remote_parent_node: Node<'t>,
                                                       remote_node: Node<'t>)
                                                       -> Result<StructureChange>
    {
        if !remote_node.is_syncable() {
            // If the remote node is known to be non-syncable, we unconditionally
            // delete it from the server, even if it's syncable locally.
            self.delete_remotely.insert(remote_node.guid.clone());
            if remote_node.is_folder() {
                // If the remote node is a folder, we also need to walk its descendants
                // and reparent any syncable descendants, and descendants that only
                // exist remotely, to the merged node.
                self.relocate_remote_orphans_to_merged_node(merged_node, remote_node)?;
            }
            return Ok(StructureChange::Deleted);
        }

        if !self.local_tree.is_deleted(&remote_node.guid) {
            if let Some(local_node) = self.local_tree.node_for_guid(&remote_node.guid) {
                if !local_node.is_syncable() {
                    // The remote node is syncable, but the local node is non-syncable.
                    // For consistency with Desktop, we unconditionally delete the
                    // node from the server.
                    self.delete_remotely.insert(remote_node.guid.clone());
                    if remote_node.is_folder() {
                        self.relocate_remote_orphans_to_merged_node(merged_node, remote_node)?;
                    }
                    return Ok(StructureChange::Deleted);
                }
                let local_parent_node =
                    local_node.parent()
                              .expect("Can't check for structure changes without local parent");
                if local_parent_node.guid != remote_parent_node.guid {
                    return Ok(StructureChange::Moved);
                }
                return Ok(StructureChange::Unchanged);
            } else {
                return Ok(StructureChange::Unchanged);
            }
        }

        if remote_node.needs_merge {
            if !remote_node.is_folder() {
                // If a non-folder child is deleted locally and changed remotely, we
                // ignore the local deletion and take the remote child.
                trace!("Remote non-folder {} deleted locally and changed remotely; taking remote \
                        change",
                       remote_node);
                self.structure_counts.remote_revives += 1;
                return Ok(StructureChange::Unchanged);
            }
            // For folders, we always take the local deletion and relocate remotely
            // changed grandchildren to the merged node. We could use the remote
            // tree to revive the child folder, but it's easier to relocate orphaned
            // grandchildren than to partially revive the child folder.
            trace!("Remote folder {} deleted locally and changed remotely; taking local deletion",
                   remote_node);
            self.structure_counts.local_deletes += 1;
        } else {
            trace!("Remote node {} deleted locally and not changed remotely; taking local \
                    deletion",
                   remote_node);
        }

        // Take the local deletion and relocate any new remote descendants to the
        // merged node.
        self.delete_remotely.insert(remote_node.guid.clone());
        if remote_node.is_folder() {
            self.relocate_remote_orphans_to_merged_node(merged_node, remote_node)?;
        }
        Ok(StructureChange::Deleted)
    }

    /// Checks if a local node is remotely moved or deleted, and reparents any
    /// descendants that aren't also locally deleted to the merged node.
    ///
    /// This is the inverse of
    /// `check_for_local_structure_change_of_remote_node`.
    fn check_for_remote_structure_change_of_local_node(&mut self,
                                                       merged_node: &mut MergedNode<'t>,
                                                       local_parent_node: Node<'t>,
                                                       local_node: Node<'t>)
                                                       -> Result<StructureChange>
    {
        if !local_node.is_syncable() {
            // If the local node is known to be non-syncable, we unconditionally
            // delete it from the local tree, even if it's syncable remotely.
            self.delete_locally.insert(local_node.guid.clone());
            if local_node.is_folder() {
                self.relocate_local_orphans_to_merged_node(merged_node, local_node)?;
            }
            return Ok(StructureChange::Deleted);
        }

        if !self.remote_tree.is_deleted(&local_node.guid) {
            if let Some(remote_node) = self.remote_tree.node_for_guid(&local_node.guid) {
                if !remote_node.is_syncable() {
                    // The local node is syncable, but the remote node is non-syncable.
                    // This can happen if we applied an orphaned left pane query in a
                    // previous sync, and later saw the left pane root on the server.
                    // Since we now have the complete subtree, we can remove the item.
                    self.delete_locally.insert(local_node.guid.clone());
                    if remote_node.is_folder() {
                        self.relocate_local_orphans_to_merged_node(merged_node, local_node)?;
                    }
                    return Ok(StructureChange::Deleted);
                }
                let remote_parent_node =
                    remote_node.parent()
                               .expect("Can't check for structure changes without remote parent");
                if remote_parent_node.guid != local_parent_node.guid {
                    return Ok(StructureChange::Moved);
                }
                return Ok(StructureChange::Unchanged);
            } else {
                return Ok(StructureChange::Unchanged);
            }
        }

        if local_node.needs_merge {
            if !local_node.is_folder() {
                trace!("Local non-folder {} deleted remotely and changed locally; taking local \
                        change",
                       local_node);
                self.structure_counts.local_revives += 1;
                return Ok(StructureChange::Unchanged);
            }
            trace!("Local folder {} deleted remotely and changed locally; taking remote deletion",
                   local_node);
            self.structure_counts.remote_deletes += 1;
        } else {
            trace!("Local node {} deleted remotely and not changed locally; taking remote \
                    deletion",
                   local_node);
        }

        // Take the remote deletion and relocate any new local descendants to the
        // merged node.
        self.delete_locally.insert(local_node.guid.clone());
        if local_node.is_folder() {
            self.relocate_local_orphans_to_merged_node(merged_node, local_node)?;
        }
        Ok(StructureChange::Deleted)
    }

    /// Takes a local deletion for a remote node by marking the node as deleted,
    /// and relocating all remote descendants that aren't also locally deleted
    /// to the closest surviving ancestor. We do this to avoid data loss if
    /// the user adds a bookmark to a folder on another device, and deletes
    /// that folder locally.
    ///
    /// This is the inverse of `relocate_local_orphans_to_merged_node`.
    fn relocate_remote_orphans_to_merged_node(&mut self,
                                              merged_node: &mut MergedNode<'t>,
                                              remote_node: Node<'t>)
                                              -> Result<()>
    {
        for remote_child_node in remote_node.children() {
            match self.check_for_local_structure_change_of_remote_node(merged_node,
                                                                       remote_node,
                                                                       remote_child_node)?
            {
                StructureChange::Moved | StructureChange::Deleted => {
                    // The remote child is already moved or deleted locally, so we should
                    // ignore it instead of treating it as a remote orphan.
                    continue;
                },
                StructureChange::Unchanged => {
                    trace!("Relocating remote orphan {} to {}",
                           remote_child_node,
                           merged_node);

                    // Flag the new parent and moved remote orphan for reupload.
                    let mut merged_orphan_node = if let Some(local_child_node) =
                        self.local_tree.node_for_guid(&remote_child_node.guid)
                    {
                        self.two_way_merge(local_child_node, remote_child_node)
                    } else {
                        self.merge_remote_node(remote_child_node)
                    }?;
                    merged_node.merge_state = merged_node.merge_state.with_new_structure();
                    merged_orphan_node.merge_state =
                        merged_orphan_node.merge_state.with_new_structure();
                    merged_node.merged_children.push(merged_orphan_node);
                },
            }
        }
        Ok(())
    }

    /// Takes a remote deletion for a local node by marking the node as deleted,
    /// and relocating all local descendants that aren't also remotely deleted
    /// to the closest surviving ancestor.
    ///
    /// This is the inverse of `relocate_remote_orphans_to_merged_node`.
    fn relocate_local_orphans_to_merged_node(&mut self,
                                             merged_node: &mut MergedNode<'t>,
                                             local_node: Node<'t>)
                                             -> Result<()>
    {
        for local_child_node in local_node.children() {
            match self.check_for_remote_structure_change_of_local_node(merged_node,
                                                                       local_node,
                                                                       local_child_node)?
            {
                StructureChange::Moved | StructureChange::Deleted => {
                    // The local child is already moved or deleted remotely, so we should
                    // ignore it instead of treating it as a local orphan.
                    continue;
                },
                StructureChange::Unchanged => {
                    trace!("Relocating local orphan {} to {}",
                           local_child_node,
                           merged_node);

                    // Flag the new parent and moved local orphan for reupload.
                    let mut merged_orphan_node = if let Some(remote_child_node) =
                        self.remote_tree.node_for_guid(&local_child_node.guid)
                    {
                        self.two_way_merge(local_child_node, remote_child_node)
                    } else {
                        self.merge_local_node(local_child_node)
                    }?;
                    merged_node.merge_state = merged_node.merge_state.with_new_structure();
                    merged_orphan_node.merge_state =
                        merged_orphan_node.merge_state.with_new_structure();
                    merged_node.merged_children.push(merged_orphan_node);
                },
            }
        }
        Ok(())
    }

    /// Finds all children of a local folder with similar content as children of
    /// the corresponding remote folder. This is used to dedupe local items that
    /// haven't been uploaded yet, to remote items that don't exist locally.
    ///
    /// Recall that we match items by GUID as we walk down the tree. If a GUID
    /// on one side doesn't exist on the other, we fall back to a content
    /// match in the same folder.
    ///
    /// This method is called the first time that
    /// `find_remote_node_matching_local_node` merges a local child that
    /// doesn't exist remotely, and
    /// the first time that `find_local_node_matching_remote_node` merges a
    /// remote child that doesn't exist locally.
    ///
    /// Finding all possible dupes is O(m + n) in the worst case, where `m` is
    /// the number of local children, and `n` is the number of remote
    /// children. We cache matches in
    /// `matching_dupes_by_local_parent_guid`, so deduping all
    /// remaining children of the same folder, on both sides, only needs two
    /// O(1) map lookups per child.
    fn find_all_matching_dupes_in_folders(&self,
                                          local_parent_node: Node<'t>,
                                          remote_parent_node: Node<'t>)
                                          -> MatchingDupes<'t>
    {
        let mut dupe_key_to_local_nodes: HashMap<&Content, VecDeque<_>> = HashMap::new();

        for local_child_node in local_parent_node.children() {
            if let Some(local_child_content) =
                self.new_local_contents
                    .and_then(|contents| contents.get(&local_child_node.guid))
            {
                if let Some(remote_child_node) =
                    self.remote_tree.node_for_guid(&local_child_node.guid)
                {
                    trace!("Not deduping local child {}; already exists remotely as {}",
                           local_child_node,
                           remote_child_node);
                    continue;
                }
                if self.remote_tree.is_deleted(&local_child_node.guid) {
                    trace!("Not deduping local child {}; deleted remotely",
                           local_child_node);
                    continue;
                }
                // Store matching local children in an array, in case multiple children
                // have the same dupe key (for example, a toolbar containing multiple
                // empty folders, as in bug 1213369).
                let local_nodes_for_key = dupe_key_to_local_nodes.entry(local_child_content)
                                                                 .or_default();
                local_nodes_for_key.push_back(local_child_node);
            } else {
                trace!("Not deduping local child {}; already uploaded",
                       local_child_node);
            }
        }

        let mut local_to_remote = HashMap::new();
        let mut remote_to_local = HashMap::new();

        for remote_child_node in remote_parent_node.children() {
            if remote_to_local.contains_key(&remote_child_node.guid) {
                trace!("Not deduping remote child {}; already deduped",
                       remote_child_node);
                continue;
            }
            // Note that we don't need to check if the remote node is deleted
            // locally, because it wouldn't have local content entries if it
            // were.
            if let Some(remote_child_content) =
                self.new_remote_contents
                    .and_then(|contents| contents.get(&remote_child_node.guid))
            {
                if let Some(mut local_nodes_for_key) =
                    dupe_key_to_local_nodes.get_mut(remote_child_content)
                {
                    if let Some(local_child_node) = local_nodes_for_key.pop_front() {
                        trace!("Deduping local child {} to remote child {}",
                               local_child_node,
                               remote_child_node);
                        local_to_remote.insert(local_child_node.guid.clone(), remote_child_node);
                        remote_to_local.insert(remote_child_node.guid.clone(), local_child_node);
                    } else {
                        trace!("Not deduping remote child {}; no remaining local content matches",
                               remote_child_node);
                        continue;
                    }
                } else {
                    trace!("Not deduping remote child {}; no local content matches",
                           remote_child_node);
                    continue;
                }
            } else {
                trace!("Not deduping remote child {}; already merged",
                       remote_child_node);
            }
        }

        (local_to_remote, remote_to_local)
    }

    /// Finds a remote node with a different GUID that matches the content of a
    /// local node.
    ///
    /// This is the inverse of `find_local_node_matching_remote_node`.
    fn find_remote_node_matching_local_node(&mut self,
                                            merged_node: &MergedNode<'t>,
                                            local_parent_node: Node<'t>,
                                            remote_parent_node: Option<Node<'t>>,
                                            local_child_node: Node<'t>)
                                            -> Option<Node<'t>>
    {
        if let Some(remote_parent_node) = remote_parent_node {
            let mut matching_dupes_by_local_parent_guid =
                mem::replace(&mut self.matching_dupes_by_local_parent_guid,
                             HashMap::new());
            let new_remote_node =
                {
                    let (local_to_remote, _) = matching_dupes_by_local_parent_guid
                    .entry(local_parent_node.guid.clone())
                    .or_insert_with(|| {
                        trace!("First local child {} doesn't exist remotely; finding all \
                                matching dupes in local {} and remote {}",
                                local_child_node,
                                local_parent_node,
                                remote_parent_node);
                        self.find_all_matching_dupes_in_folders(
                            local_parent_node,
                            remote_parent_node,
                        )
                    });
                    let new_remote_node = local_to_remote.get(&local_child_node.guid);
                    new_remote_node.map(|node| {
                        self.structure_counts.dupes += 1;
                        *node
                    })
                };
            mem::replace(&mut self.matching_dupes_by_local_parent_guid,
                         matching_dupes_by_local_parent_guid);
            new_remote_node
        } else {
            trace!("Merged node {} doesn't exist remotely; no potential dupes for local child {}",
                   merged_node,
                   local_child_node);
            None
        }
    }

    /// Finds a local node with a different GUID that matches the content of a
    /// remote node.
    ///
    /// This is the inverse of `find_remote_node_matching_local_node`.
    fn find_local_node_matching_remote_node(&mut self,
                                            merged_node: &MergedNode<'t>,
                                            local_parent_node: Option<Node<'t>>,
                                            remote_parent_node: Node<'t>,
                                            remote_child_node: Node<'t>)
                                            -> Option<Node<'t>>
    {
        if let Some(local_parent_node) = local_parent_node {
            let mut matching_dupes_by_local_parent_guid =
                mem::replace(&mut self.matching_dupes_by_local_parent_guid,
                             HashMap::new());
            let new_local_node =
                {
                    let (_, remote_to_local) = matching_dupes_by_local_parent_guid
                    .entry(local_parent_node.guid.clone())
                    .or_insert_with(|| {
                        trace!("First remote child {} doesn't exist locally; finding all \
                                matching dupes in local {} and remote {}",
                                remote_child_node,
                                local_parent_node,
                                remote_parent_node);
                        self.find_all_matching_dupes_in_folders(
                            local_parent_node,
                            remote_parent_node,
                        )
                    });
                    let new_local_node = remote_to_local.get(&remote_child_node.guid);
                    new_local_node.map(|node| {
                        self.structure_counts.dupes += 1;
                        *node
                    })
                };
            mem::replace(&mut self.matching_dupes_by_local_parent_guid,
                         matching_dupes_by_local_parent_guid);
            new_local_node
        } else {
            trace!("Merged node {} doesn't exist locally; no potential dupes for remote child {}",
                   merged_node,
                   remote_child_node);
            None
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate env_logger;

    use super::*;
    use std::sync::Once;

    use guid::ROOT_GUID;
    use tree::{Item, Kind};

    #[derive(Debug)]
    struct Node {
        item: Item,
        children: Vec<Box<Node>>,
    }

    impl Node {
        fn new(item: Item) -> Node {
            Node { item, children: Vec::new() }
        }

        fn into_tree(self) -> Result<Tree> {
            fn inflate(tree: &mut Tree, parent_guid: &Guid, node: Node) -> Result<()> {
                let guid = node.item.guid.clone();
                tree.insert(&parent_guid, node.item)?;
                for child in node.children {
                    inflate(tree, &guid, *child)?;
                }
                Ok(())
            }

            let guid = self.item.guid.clone();
            let mut tree = Tree::new(self.item);
            for child in self.children {
                inflate(&mut tree, &guid, *child)?;
            }
            Ok(tree)
        }
    }

    macro_rules! nodes {
        ($children:tt) => { nodes!(ROOT_GUID, Folder, $children) };
        ($guid:expr, $kind:ident) => { nodes!(Guid::from($guid), $kind[]) };
        ($guid:expr, $kind:ident [ $( $name:ident = $value:expr ),* ]) => {{
            let mut item = Item::new(Guid::from($guid), Kind::$kind);
            $({ item.$name = $value; })*
            Node::new(item)
        }};
        ($guid:expr, $kind:ident, $children:tt) => { nodes!($guid, $kind[], $children) };
        ($guid:expr, $kind:ident [ $( $name:ident = $value:expr ),* ], { $(( $($children:tt)+ )),* }) => {{
            let mut node = nodes!($guid, $kind [ $( $name = $value ),* ]);
            $({
                let child = nodes!($($children)*);
                node.children.push(child.into());
            })*
            node
        }};
    }

    fn before_each() {
        static ONCE: Once = Once::new();
        ONCE.call_once(|| {
                           env_logger::init();
                       });
    }

    #[test]
    fn reparent_and_reposition() {
        before_each();

        let local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("folderAAAAAA", Folder[needs_merge = true], {
                    ("bookmarkAAAA", Bookmark[needs_merge = true]),
                    ("folderBBBBBB", Folder[needs_merge = true], {
                        ("bookmarkCCCC", Bookmark[needs_merge = true]),
                        ("bookmarkDDDD", Bookmark[needs_merge = true])
                    }),
                    ("bookmarkEEEE", Bookmark[needs_merge = true])
                }),
                ("bookmarkFFFF", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();

        let remote_tree = nodes!({
            ("unfiled_____", Folder[needs_merge = true], {
                ("folderBBBBBB", Folder[needs_merge = true], {
                    ("bookmarkDDDD", Bookmark[needs_merge = true]),
                    ("bookmarkAAAA", Bookmark[needs_merge = true]),
                    ("bookmarkCCCC", Bookmark[needs_merge = true])
                })
            }),
            ("toolbar_____", Folder[needs_merge = true], {
                ("folderAAAAAA", Folder, {
                    ("bookmarkFFFF", Bookmark[needs_merge = true]),
                    ("bookmarkEEEE", Bookmark[needs_merge = true])
                })
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!(ROOT_GUID, Folder[needs_merge = true], {
            ("unfiled_____", Folder, {
                ("folderBBBBBB", Folder, {
                    ("bookmarkDDDD", Bookmark),
                    ("bookmarkAAAA", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                })
            }),
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder[needs_merge = true], {
                    ("bookmarkEEEE", Bookmark)
                })
            }),
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkFFFF", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    // This test moves a bookmark that exists locally into a new folder that only
    // exists remotely, and is a later sibling of the local parent.
    #[test]
    fn move_into_parent_sibling() {
        before_each();

        let local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("folderAAAAAA", Folder[needs_merge = true], {
                    ("bookmarkBBBB", Bookmark[needs_merge = true])
                })
            })
        }).into_tree().unwrap();

        let remote_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("folderAAAAAA", Folder[needs_merge = true]),
                ("folderCCCCCC", Folder[needs_merge = true], {
                    ("bookmarkBBBB", Bookmark[needs_merge = true])
                })
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder),
                ("folderCCCCCC", Folder, {
                    ("bookmarkBBBB", Bookmark)
                })
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn reorder_and_insert() {
        before_each();

        let _shared_tree = nodes!({
            ("menu________", Folder, {
                ("bookmarkAAAA", Bookmark),
                ("bookmarkBBBB", Bookmark),
                ("bookmarkCCCC", Bookmark)
            }),
            ("toolbar_____", Folder, {
                ("bookmarkDDDD", Bookmark),
                ("bookmarkEEEE", Bookmark),
                ("bookmarkFFFF", Bookmark)
            })
        }).into_tree().unwrap();

        let local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkCCCC", Bookmark),
                ("bookmarkAAAA", Bookmark),
                ("bookmarkBBBB", Bookmark)
            }),
            ("toolbar_____", Folder[needs_merge = true, age = 5], {
                ("bookmarkDDDD", Bookmark),
                ("bookmarkEEEE", Bookmark),
                ("bookmarkFFFF", Bookmark),
                ("bookmarkGGGG", Bookmark[needs_merge = true]),
                ("bookmarkHHHH", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();

        let remote_tree = nodes!({
            ("menu________", Folder[needs_merge = true, age = 5], {
                ("bookmarkAAAA", Bookmark[age = 5]),
                ("bookmarkBBBB", Bookmark[age = 5]),
                ("bookmarkCCCC", Bookmark[age = 5]),
                ("bookmarkIIII", Bookmark[needs_merge = true]),
                ("bookmarkJJJJ", Bookmark[needs_merge = true])
            }),
            ("toolbar_____", Folder[needs_merge = true], {
                ("bookmarkFFFF", Bookmark),
                ("bookmarkDDDD", Bookmark),
                ("bookmarkEEEE", Bookmark)
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                // The server has an older menu, so we should use the local order (C A B)
                // as the base, then append (I J).
                ("bookmarkCCCC", Bookmark),
                ("bookmarkAAAA", Bookmark),
                ("bookmarkBBBB", Bookmark),
                ("bookmarkIIII", Bookmark),
                ("bookmarkJJJJ", Bookmark)
            }),
            ("toolbar_____", Folder[needs_merge = true, age = 5], {
                // The server has a newer toolbar, so we should use the remote order (F D E)
                // as the base, then append (G H).
                ("bookmarkFFFF", Bookmark),
                ("bookmarkDDDD", Bookmark),
                ("bookmarkEEEE", Bookmark),
                ("bookmarkGGGG", Bookmark[needs_merge = true]),
                ("bookmarkHHHH", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn value_structure_conflict() {
        before_each();

        let _shared_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                }),
                ("folderDDDDDD", Folder, {
                    ("bookmarkEEEE", Bookmark)
                })
            })
        }).into_tree().unwrap();

        let local_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder[needs_merge = true, age = 10], {
                    ("bookmarkCCCC", Bookmark)
                }),
                ("folderDDDDDD", Folder[needs_merge = true, age = 10], {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkEEEE", Bookmark[age = 10])
                })
            })
        }).into_tree().unwrap();

        let remote_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                }),
                ("folderDDDDDD", Folder[needs_merge = true, age = 5], {
                    ("bookmarkEEEE", Bookmark[needs_merge = true, age = 5])
                })
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder[needs_merge = true, age = 10], {
                    ("bookmarkCCCC", Bookmark)
                }),
                ("folderDDDDDD", Folder[needs_merge = true, age = 5], {
                    ("bookmarkEEEE", Bookmark[age = 5]),
                    ("bookmarkBBBB", Bookmark[needs_merge = true])
                })
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn complex_move_with_additions() {
        before_each();

        let _shared_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                })
            })
        }).into_tree().unwrap();

        let local_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark),
                    ("bookmarkDDDD", Bookmark)
                })
            })
        }).into_tree().unwrap();

        let remote_tree = nodes!({
            ("menu________", Folder, {
                ("bookmarkCCCC", Bookmark)
            }),
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkEEEE", Bookmark)
                })
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder, {
                ("bookmarkCCCC", Bookmark)
            }),
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder[needs_merge = true], {
                    // We can guarantee child order (B E D), since we always walk remote
                    // children first, and the remote folder A record is newer than the
                    // local folder. If the local folder were newer, the order would be
                    // (D B E).
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkEEEE", Bookmark),
                    ("bookmarkDDDD", Bookmark[needs_merge = true])
                })
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn complex_orphaning() {
        before_each();

        let _shared_tree = nodes!({
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder, {
                    ("folderBBBBBB", Folder)
                })
            }),
            ("menu________", Folder, {
                ("folderCCCCCC", Folder, {
                    ("folderDDDDDD", Folder, {
                        ("folderEEEEEE", Folder)
                    })
                })
            })
        }).into_tree().unwrap();

        // Locally: delete E, add B > F.
        let mut local_tree = nodes!({
            ("toolbar_____", Folder[needs_merge = false], {
                ("folderAAAAAA", Folder, {
                    ("folderBBBBBB", Folder[needs_merge = true], {
                        ("bookmarkFFFF", Bookmark[needs_merge = true])
                    })
                })
            }),
            ("menu________", Folder, {
                ("folderCCCCCC", Folder, {
                    ("folderDDDDDD", Folder[needs_merge = true])
                })
            })
        }).into_tree().unwrap();
        local_tree.note_deleted("folderEEEEEE".into());

        // Remotely: delete B, add E > G.
        let mut remote_tree = nodes!({
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder[needs_merge = true])
            }),
            ("menu________", Folder, {
                ("folderCCCCCC", Folder, {
                    ("folderDDDDDD", Folder, {
                        ("folderEEEEEE", Folder[needs_merge = true], {
                            ("bookmarkGGGG", Bookmark[needs_merge = true])
                        })
                    })
                })
            })
        }).into_tree().unwrap();
        remote_tree.note_deleted("folderBBBBBB".into());

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder[needs_merge = true], {
                    // B was deleted remotely, so F moved to A, the closest
                    // surviving parent.
                    ("bookmarkFFFF", Bookmark[needs_merge = true])
                })
            }),
            ("menu________", Folder, {
                ("folderCCCCCC", Folder, {
                    ("folderDDDDDD", Folder[needs_merge = true], {
                        // E was deleted locally, so G moved to D.
                        ("bookmarkGGGG", Bookmark[needs_merge = true])
                    })
                })
            })
        }).into_tree().unwrap();
        let expected_deletions = vec![
            "folderBBBBBB",
            "folderEEEEEE",
        ].into_iter().map(|guid| guid.into()).collect::<Vec<Guid>>();
        let expected_telem = StructureCounts {
            remote_revives: 0,
            local_deletes: 1,
            local_revives: 0,
            remote_deletes: 1,
            dupes: 0,
        };

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        let mut deletions = merger.deletions().map(|d| d.guid).collect::<Vec<Guid>>();
        deletions.sort_unstable();
        assert_eq!(deletions, expected_deletions);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn locally_modified_remotely_deleted() {
        before_each();

        let _shared_tree = nodes!({
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder, {
                    ("folderBBBBBB", Folder)
                })
            }),
            ("menu________", Folder, {
                ("folderCCCCCC", Folder, {
                    ("folderDDDDDD", Folder, {
                        ("folderEEEEEE", Folder)
                    })
                })
            })
        }).into_tree().unwrap();

        let mut local_tree = nodes!({
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder, {
                    ("folderBBBBBB", Folder[needs_merge = true], {
                        ("bookmarkFFFF", Bookmark[needs_merge = true])
                    })
                })
            }),
            ("menu________", Folder, {
                ("folderCCCCCC", Folder, {
                    ("folderDDDDDD", Folder[needs_merge = true])
                })
            })
        }).into_tree().unwrap();
        local_tree.note_deleted("folderEEEEEE".into());

        let mut remote_tree = nodes!({
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder[needs_merge = true])
            }),
            ("menu________", Folder, {
                ("folderCCCCCC", Folder, {
                    ("folderDDDDDD", Folder, {
                        ("folderEEEEEE", Folder[needs_merge = true], {
                            ("bookmarkGGGG", Bookmark[needs_merge = true])
                        })
                    })
                })
            })
        }).into_tree().unwrap();
        remote_tree.note_deleted("folderBBBBBB".into());

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder[needs_merge = true], {
                    ("bookmarkFFFF", Bookmark[needs_merge = true])
                })
            }),
            ("menu________", Folder, {
                ("folderCCCCCC", Folder, {
                    ("folderDDDDDD", Folder[needs_merge = true], {
                        ("bookmarkGGGG", Bookmark[needs_merge = true])
                    })
                })
            })
        }).into_tree().unwrap();
        let expected_deletions = vec![
            "folderBBBBBB",
            "folderEEEEEE",
        ].into_iter().map(|guid| guid.into()).collect::<Vec<Guid>>();
        let expected_telem = StructureCounts {
            remote_revives: 0,
            local_deletes: 1,
            local_revives: 0,
            remote_deletes: 1,
            dupes: 0,
        };

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        let mut deletions = merger.deletions().map(|d| d.guid).collect::<Vec<Guid>>();
        deletions.sort();
        assert_eq!(deletions, expected_deletions);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn locally_deleted_remotely_modified() {
        before_each();

        let _shared_tree = nodes!({
            ("menu________", Folder, {
                ("bookmarkAAAA", Bookmark),
                ("folderBBBBBB", Folder, {
                    ("bookmarkCCCC", Bookmark),
                    ("folderDDDDDD", Folder, {
                        ("bookmarkEEEE", Bookmark)
                    })
                })
            })
        }).into_tree().unwrap();

        let mut local_tree = nodes!({
            ("menu________", Folder[needs_merge = true])
        }).into_tree().unwrap();
        for guid in &["bookmarkAAAA", "folderBBBBBB", "bookmarkCCCC", "folderDDDDDD", "bookmarkEEEE"] {
            local_tree.note_deleted(guid.to_owned().into());
        }

        let remote_tree = nodes!({
            ("menu________", Folder, {
                ("bookmarkAAAA", Bookmark[needs_merge = true]),
                ("folderBBBBBB", Folder[needs_merge = true], {
                    ("bookmarkCCCC", Bookmark),
                    ("folderDDDDDD", Folder[needs_merge = true], {
                        ("bookmarkEEEE", Bookmark),
                        ("bookmarkFFFF", Bookmark[needs_merge = true])
                    }),
                    ("bookmarkGGGG", Bookmark[needs_merge = true])
                })
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkAAAA", Bookmark),
                ("bookmarkFFFF", Bookmark[needs_merge = true]),
                ("bookmarkGGGG", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        let expected_deletions = vec![
            "bookmarkCCCC",
            "bookmarkEEEE",
            "folderBBBBBB",
            "folderDDDDDD",
        ].into_iter().map(|guid| guid.into()).collect::<Vec<Guid>>();
        let expected_telem = StructureCounts {
            remote_revives: 1,
            local_deletes: 2,
            local_revives: 0,
            remote_deletes: 0,
            dupes: 0,
        };

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        let mut deletions = merger.deletions().map(|d| d.guid).collect::<Vec<Guid>>();
        deletions.sort();
        assert_eq!(deletions, expected_deletions);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn nonexistent_on_one_side() {
        before_each();

        let mut local_tree = Tree::default();
        // A doesn't exist remotely.
        local_tree.note_deleted("bookmarkAAAA".into());

        let mut remote_tree = Tree::default();
        // B doesn't exist locally.
        remote_tree.note_deleted("bookmarkBBBB".into());

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = Tree::default();
        let expected_deletions = vec![
            "bookmarkAAAA",
            "bookmarkBBBB",
        ].into_iter().map(|guid| guid.into()).collect::<Vec<Guid>>();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        let mut deletions = merger.deletions().map(|d| d.guid).collect::<Vec<Guid>>();
        deletions.sort();
        assert_eq!(deletions, expected_deletions);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn clear_folder_then_delete() {
        before_each();

        let _shared_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                }),
                ("folderDDDDDD", Folder, {
                    ("bookmarkEEEE", Bookmark),
                    ("bookmarkFFFF", Bookmark)
                })
            })
        }).into_tree().unwrap();

        let mut local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                }),
                ("bookmarkEEEE", Bookmark[needs_merge = true])
            }),
            ("mobile______", Folder[needs_merge = true], {
                ("bookmarkFFFF", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        local_tree.note_deleted("folderDDDDDD".into());

        let mut remote_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkBBBB", Bookmark[needs_merge = true]),
                ("folderDDDDDD", Folder, {
                    ("bookmarkEEEE", Bookmark),
                    ("bookmarkFFFF", Bookmark)
                })
            }),
            ("unfiled_____", Folder[needs_merge = true], {
                ("bookmarkCCCC", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        remote_tree.note_deleted("folderAAAAAA".into());

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!(ROOT_GUID, Folder[needs_merge = true], {
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkBBBB", Bookmark),
                ("bookmarkEEEE", Bookmark[needs_merge = true])
            }),
            ("unfiled_____", Folder, {
                ("bookmarkCCCC", Bookmark)
            }),
            ("mobile______", Folder[needs_merge = true], {
                ("bookmarkFFFF", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        let expected_deletions = vec![
            "folderAAAAAA",
            "folderDDDDDD",
        ].into_iter().map(|guid| guid.into()).collect::<Vec<Guid>>();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        let mut deletions = merger.deletions().map(|d| d.guid).collect::<Vec<Guid>>();
        deletions.sort();
        assert_eq!(deletions, expected_deletions);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn newer_move_to_deleted() {
        before_each();

        let _shared_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark)
                }),
                ("folderCCCCCC", Folder, {
                    ("bookmarkDDDD", Bookmark)
                })
            })
        }).into_tree().unwrap();

        let mut local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                // A is younger locally. However, we should *not* revert
                // remotely moving B to the toolbar. (Locally, B exists in A,
                // but we deleted the now-empty A remotely).
                ("folderAAAAAA", Folder[needs_merge = true], {
                    ("bookmarkBBBB", Bookmark[age = 5]),
                    ("bookmarkEEEE", Bookmark[needs_merge = true])
                })
            }),
            ("toolbar_____", Folder[needs_merge = true], {
                ("bookmarkDDDD", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        local_tree.note_deleted("folderCCCCCC".into());

        let mut remote_tree = nodes!({
            ("menu________", Folder[needs_merge = true, age = 5], {
                // C is younger remotely. However, we should *not* revert
                // locally moving D to the toolbar. (Locally, D exists in C,
                // but we deleted the now-empty C locally).
                ("folderCCCCCC", Folder[needs_merge = true], {
                    ("bookmarkDDDD", Bookmark[age = 5]),
                    ("bookmarkFFFF", Bookmark[needs_merge = true])
                })
            }),
            ("toolbar_____", Folder[needs_merge = true, age = 5], {
                ("bookmarkBBBB", Bookmark[needs_merge = true, age = 5])
            })
        }).into_tree().unwrap();
        remote_tree.note_deleted("folderAAAAAA".into());

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkEEEE", Bookmark[needs_merge = true]),
                ("bookmarkFFFF", Bookmark[needs_merge = true])
            }),
            ("toolbar_____", Folder[needs_merge = true], {
                ("bookmarkDDDD", Bookmark[needs_merge = true]),
                ("bookmarkBBBB", Bookmark[age = 5])
            })
        }).into_tree().unwrap();
        let expected_deletions = vec![
            "folderAAAAAA",
            "folderCCCCCC",
        ].into_iter().map(|guid| guid.into()).collect::<Vec<Guid>>();
        let expected_telem = StructureCounts {
            remote_revives: 0,
            local_deletes: 1,
            local_revives: 0,
            remote_deletes: 1,
            dupes: 0,
        };

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        let mut deletions = merger.deletions().map(|d| d.guid).collect::<Vec<Guid>>();
        deletions.sort();
        assert_eq!(deletions, expected_deletions);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn deduping_local_newer() {
        before_each();

        let local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkAAA1", Bookmark[needs_merge = true]),
                ("bookmarkAAA2", Bookmark[needs_merge = true]),
                ("bookmarkAAA3", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        let mut new_local_contents: HashMap<Guid, Content> = HashMap::new();
        new_local_contents.insert("bookmarkAAA1".into(),
                                  Content::Bookmark { title: "A".into(),
                                                      url_href: "http://example.com/a".into(), });
        new_local_contents.insert("bookmarkAAA2".into(),
                                  Content::Bookmark { title: "A".into(),
                                                      url_href: "http://example.com/a".into(), });
        new_local_contents.insert("bookmarkAAA3".into(),
                                  Content::Bookmark { title: "A".into(),
                                                      url_href: "http://example.com/a".into(), });

        let remote_tree = nodes!({
            ("menu________", Folder[needs_merge = true, age = 5], {
                ("bookmarkAAAA", Bookmark[needs_merge = true, age = 5]),
                ("bookmarkAAA4", Bookmark[needs_merge = true, age = 5]),
                ("bookmarkAAA5", Bookmark)
            })
        }).into_tree().unwrap();
        let mut new_remote_contents: HashMap<Guid, Content> = HashMap::new();
        new_remote_contents.insert("bookmarkAAAA".into(),
                                   Content::Bookmark { title: "A".into(),
                                                       url_href: "http://example.com/a".into(), });
        new_remote_contents.insert("bookmarkAAA4".into(),
                                   Content::Bookmark { title: "A".into(),
                                                       url_href: "http://example.com/a".into(), });

        let mut merger = Merger::with_contents(&local_tree,
                                               &new_local_contents,
                                               &remote_tree,
                                               &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkAAAA", Bookmark),
                ("bookmarkAAA4", Bookmark),
                ("bookmarkAAA3", Bookmark[needs_merge = true]),
                ("bookmarkAAA5", Bookmark)
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts {
            remote_revives: 0,
            local_deletes: 0,
            local_revives: 0,
            remote_deletes: 0,
            dupes: 2,
        };

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn deduping_remote_newer() {
        before_each();

        let local_tree = nodes!({
            ("menu________", Folder[needs_merge = true, age = 5], {
                // Shouldn't dedupe to `folderAAAAA1` because it's not in
                // `new_local_contents`.
                ("folderAAAAAA", Folder[needs_merge = true, age = 5], {
                    // Shouldn't dedupe to `bookmarkBBB1`. (bookmarkG111)
                    ("bookmarkBBBB", Bookmark[age = 10]),
                    // Not a candidate for `bookmarkCCC1` because the URLs are
                    // different. (bookmarkH111)
                    ("bookmarkCCCC", Bookmark[needs_merge = true, age = 5])
                }),
                // Should dedupe to `folderDDDDD1`. (folderB11111)
                ("folderDDDDDD", Folder[needs_merge = true, age = 5], {
                    // Should dedupe to `bookmarkEEE1`. (bookmarkC222)
                    ("bookmarkEEEE", Bookmark[needs_merge = true, age = 5]),
                    // Should dedupe to `separatorFF1` because the positions are
                    // the same. (separatorF11)
                    ("separatorFFF", Separator[needs_merge = true, age = 5])
                }),
                // Shouldn't dedupe to `separatorGG1`, because the positions are
                // different. (separatorE11)
                ("separatorGGG", Separator[needs_merge = true, age = 5]),
                // Shouldn't dedupe to `bookmarkHHH1` because the parents are
                // different. (bookmarkC222)
                ("bookmarkHHHH", Bookmark[needs_merge = true, age = 5]),
                // Should dedupe to `queryIIIIII1`.
                ("queryIIIIIII", Query[needs_merge = true, age = 5])
            })
        }).into_tree().unwrap();
        let mut new_local_contents: HashMap<Guid, Content> = HashMap::new();
        new_local_contents.insert("bookmarkCCCC".into(),
                                  Content::Bookmark { title: "C".into(),
                                                      url_href: "http://example.com/c".into() });
        new_local_contents.insert("folderDDDDDD".into(),
                                  Content::Folder { title: "D".into() });
        new_local_contents.insert("bookmarkEEEE".into(),
                                  Content::Bookmark { title: "E".into(),
                                                      url_href: "http://example.com/e".into() });
        new_local_contents.insert("separatorFFF".into(), Content::Separator { position: 1 });
        new_local_contents.insert("separatorGGG".into(), Content::Separator { position: 2 });
        new_local_contents.insert("bookmarkHHHH".into(),
                                  Content::Bookmark { title: "H".into(),
                                                      url_href: "http://example.com/h".into() });
        new_local_contents.insert("queryIIIIIII".into(),
                                  Content::Bookmark { title: "I".into(),
                                                      url_href: "place:maxResults=10&sort=8".into() });

        let remote_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("folderAAAAAA", Folder[needs_merge = true], {
                    ("bookmarkBBBB", Bookmark[age = 10]),
                    ("bookmarkCCC1", Bookmark[needs_merge = true])
                }),
                ("folderDDDDD1", Folder[needs_merge = true], {
                    ("bookmarkEEE1", Bookmark[needs_merge = true]),
                    ("separatorFF1", Separator[needs_merge = true])
                }),
                ("separatorGG1", Separator[needs_merge = true]),
                ("bookmarkHHH1", Bookmark[needs_merge = true]),
                ("queryIIIIII1", Query[needs_merge = true])
            })
        }).into_tree().unwrap();
        let mut new_remote_contents: HashMap<Guid, Content> = HashMap::new();
        new_remote_contents.insert("bookmarkCCC1".into(),
                                   Content::Bookmark { title: "C".into(),
                                                       url_href: "http://example.com/c1".into() });
        new_remote_contents.insert("folderDDDDD1".into(),
                                   Content::Folder { title: "D".into() });
        new_remote_contents.insert("bookmarkEEE1".into(),
                                   Content::Bookmark { title: "E".into(),
                                                       url_href: "http://example.com/e".into() });
        new_remote_contents.insert("separatorFF1".into(), Content::Separator { position: 1 });
        new_remote_contents.insert("separatorGG1".into(), Content::Separator { position: 2 });
        new_remote_contents.insert("bookmarkHHH1".into(),
                                   Content::Bookmark { title: "H".into(),
                                                       url_href: "http://example.com/h".into() });
        new_remote_contents.insert("queryIIIIII1".into(),
                                   Content::Bookmark { title: "I".into(),
                                                       url_href: "place:maxResults=10&sort=8".into() });

        let mut merger = Merger::with_contents(&local_tree,
                                               &new_local_contents,
                                               &remote_tree,
                                               &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder[age = 5], {
                ("folderAAAAAA", Folder[needs_merge = true], {
                    ("bookmarkBBBB", Bookmark[age = 10]),
                    ("bookmarkCCC1", Bookmark),
                    ("bookmarkCCCC", Bookmark[needs_merge = true, age = 5])
                }),
                ("folderDDDDD1", Folder, {
                    ("bookmarkEEE1", Bookmark),
                    ("separatorFF1", Separator)
                }),
                ("separatorGG1", Separator),
                ("bookmarkHHH1", Bookmark),
                ("queryIIIIII1", Query)
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts {
            remote_revives: 0,
            local_deletes: 0,
            local_revives: 0,
            remote_deletes: 0,
            dupes: 6,
        };

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn complex_deduping() {
        before_each();

        let local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("folderAAAAAA", Folder[needs_merge = true, age = 10], {
                    ("bookmarkBBBB", Bookmark[needs_merge = true, age = 10]),
                    ("bookmarkCCCC", Bookmark[needs_merge = true, age = 10])
                }),
                ("folderDDDDDD", Folder[needs_merge = true], {
                    ("bookmarkEEEE", Bookmark[needs_merge = true, age = 5])
                }),
                ("folderFFFFFF", Folder[needs_merge = true, age = 5], {
                    ("bookmarkGGGG", Bookmark[needs_merge = true, age = 5])
                })
            })
        }).into_tree().unwrap();
        let mut new_local_contents: HashMap<Guid, Content> = HashMap::new();
        new_local_contents.insert("folderAAAAAA".into(),
                                  Content::Folder { title: "A".into() });
        new_local_contents.insert("bookmarkBBBB".into(),
                                  Content::Bookmark { title: "B".into(),
                                                      url_href: "http://example.com/b".into() });
        new_local_contents.insert("bookmarkCCCC".into(),
                                  Content::Bookmark { title: "C".into(),
                                                      url_href: "http://example.com/c".into() });
        new_local_contents.insert("folderDDDDDD".into(),
                                  Content::Folder { title: "D".into() });
        new_local_contents.insert("bookmarkEEEE".into(),
                                  Content::Bookmark { title: "E".into(),
                                                      url_href: "http://example.com/e".into() });
        new_local_contents.insert("folderFFFFFF".into(),
                                  Content::Folder { title: "F".into() });
        new_local_contents.insert("bookmarkGGGG".into(),
                                  Content::Bookmark { title: "G".into(),
                                                      url_href: "http://example.com/g".into() });

        let remote_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("folderAAAAA1", Folder[needs_merge = true], {
                    ("bookmarkBBB1", Bookmark[needs_merge = true])
                }),
                ("folderDDDDD1", Folder[needs_merge = true, age = 5], {
                    ("bookmarkEEE1", Bookmark[needs_merge = true])
                }),
                ("folderFFFFF1", Folder[needs_merge = true], {
                    ("bookmarkGGG1", Bookmark[needs_merge = true, age = 5]),
                    ("bookmarkHHH1", Bookmark[needs_merge = true])
                })
            })
        }).into_tree().unwrap();
        let mut new_remote_contents: HashMap<Guid, Content> = HashMap::new();
        new_remote_contents.insert("folderAAAAA1".into(),
                                   Content::Folder { title: "A".into() });
        new_remote_contents.insert("bookmarkBBB1".into(),
                                   Content::Bookmark { title: "B".into(),
                                                       url_href: "http://example.com/b".into() });
        new_remote_contents.insert("folderDDDDD1".into(),
                                   Content::Folder { title: "D".into() });
        new_remote_contents.insert("bookmarkEEE1".into(),
                                   Content::Bookmark { title: "E".into(),
                                                       url_href: "http://example.com/e".into() });
        new_remote_contents.insert("folderFFFFF1".into(),
                                   Content::Folder { title: "F".into() });
        new_remote_contents.insert("bookmarkGGG1".into(),
                                   Content::Bookmark { title: "G".into(),
                                                       url_href: "http://example.com/g".into() });
        new_remote_contents.insert("bookmarkHHH1".into(),
                                   Content::Bookmark { title: "H".into(),
                                                       url_href: "http://example.com/h".into() });

        let mut merger = Merger::with_contents(&local_tree,
                                               &new_local_contents,
                                               &remote_tree,
                                               &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAA1", Folder[needs_merge = true], {
                    ("bookmarkBBB1", Bookmark),
                    ("bookmarkCCCC", Bookmark[needs_merge = true, age = 10])
                }),
                ("folderDDDDD1", Folder, {
                    ("bookmarkEEE1", Bookmark)
                }),
                ("folderFFFFF1", Folder, {
                    ("bookmarkGGG1", Bookmark[age = 5]),
                    ("bookmarkHHH1", Bookmark)
                })
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts {
            remote_revives: 0,
            local_deletes: 0,
            local_revives: 0,
            remote_deletes: 0,
            dupes: 6,
        };

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn left_pane_root() {
        before_each();

        let local_tree = Tree::default();

        let remote_tree = nodes!({
            ("folderLEFTPR", Folder[needs_merge = true], {
                ("folderLEFTPQ", Query[needs_merge = true]),
                ("folderLEFTPF", Folder[needs_merge = true], {
                    ("folderLEFTPC", Query[needs_merge = true])
                })
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!(ROOT_GUID, Folder[needs_merge = true]).into_tree().unwrap();
        let expected_deletions = vec![
            "folderLEFTPC",
            "folderLEFTPF",
            "folderLEFTPQ",
            "folderLEFTPR",
        ].into_iter().map(|guid| guid.into()).collect::<Vec<Guid>>();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        let mut deletions = merger.deletions().map(|d| d.guid).collect::<Vec<Guid>>();
        deletions.sort();
        assert_eq!(deletions, expected_deletions);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn non_syncable_items() {
        before_each();

        let local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                // A is non-syncable remotely, but B doesn't exist remotely, so
                // we'll remove A from the merged structure, and move B to the
                // menu.
                ("folderAAAAAA", Folder[needs_merge = true], {
                    ("bookmarkBBBB", Bookmark[needs_merge = true])
                })
            }),
            ("unfiled_____", Folder, {
                // Orphaned left pane queries.
                ("folderLEFTPQ", Query),
                ("folderLEFTPC", Query)
            }),
            ("rootCCCCCCCC", Folder, {
                // Non-syncable local root and children.
                ("folderDDDDDD", Folder, {
                    ("bookmarkEEEE", Bookmark)
                }),
                ("bookmarkFFFF", Bookmark)
            })
        }).into_tree().unwrap();

        let remote_tree = nodes!({
            ("unfiled_____", Folder[needs_merge = true], {
                // D, J, and G are syncable remotely, but D is non-syncable
                // locally. Since J and G don't exist locally, and are syncable
                // remotely, we'll remove D, and move J and G to unfiled.
                ("folderDDDDDD", Folder[needs_merge = true], {
                    ("bookmarkJJJJ", Bookmark[needs_merge = true])
                }),
                ("bookmarkGGGG", Bookmark)
            }),
            ("rootHHHHHHHH", Folder[needs_merge = true], {
                // H is a non-syncable root that only exists remotely. A is
                // non-syncable remotely, and syncable locally. We should
                // remove A and its descendants locally, since its parent
                // H is known to be non-syncable remotely.
                ("folderAAAAAA", Folder, {
                    // F exists in two different non-syncable folders: C
                    // locally, and A remotely.
                    ("bookmarkFFFF", Bookmark),
                    ("bookmarkIIII", Bookmark)
                })
            }),
            ("folderLEFTPR", Folder[needs_merge = true], {
                // The complete left pane root. We should remove all left pane
                // queries locally, even though they're syncable, since the left
                // pane root is known to be non-syncable.
                ("folderLEFTPQ", Query[needs_merge = true]),
                ("folderLEFTPF", Folder[needs_merge = true], {
                    ("folderLEFTPC", Query[needs_merge = true])
                })
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!(ROOT_GUID, Folder[needs_merge = true], {
            ("unfiled_____", Folder[needs_merge = true], {
                ("bookmarkJJJJ", Bookmark[needs_merge = true]),
                ("bookmarkGGGG", Bookmark)
            }),
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkBBBB", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        let expected_deletions = vec![
            "bookmarkEEEE", // Non-syncable locally.
            "bookmarkFFFF", // Non-syncable locally.
            "bookmarkIIII", // Non-syncable remotely.
            "folderAAAAAA", // Non-syncable remotely.
            "folderDDDDDD", // Non-syncable locally.
            "folderLEFTPC", // Non-syncable remotely.
            "folderLEFTPF", // Non-syncable remotely.
            "folderLEFTPQ", // Non-syncable remotely.
            "folderLEFTPR", // Non-syncable remotely.
            "rootCCCCCCCC", // Non-syncable locally.
            "rootHHHHHHHH", // Non-syncable remotely.
        ].into_iter().map(|guid| guid.into()).collect::<Vec<Guid>>();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        let mut deletions = merger.deletions().map(|d| d.guid).collect::<Vec<Guid>>();
        deletions.sort();
        assert_eq!(deletions, expected_deletions);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn applying_two_empty_folders_doesnt_smush() {
        before_each();

        let local_tree = Tree::default();

        let remote_tree = nodes!({
            ("mobile______", Folder[needs_merge = true], {
                ("emptyempty01", Folder[needs_merge = true]),
                ("emptyempty02", Folder[needs_merge = true])
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("mobile______", Folder, {
                ("emptyempty01", Folder),
                ("emptyempty02", Folder)
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn applying_two_empty_folders_matches_only_one() {
        before_each();

        let local_tree = nodes!({
            ("mobile______", Folder[needs_merge = true], {
                ("emptyempty02", Folder[needs_merge = true]),
                ("emptyemptyL0", Folder[needs_merge = true])
            })
        }).into_tree().unwrap();
        let mut new_local_contents: HashMap<Guid, Content> = HashMap::new();
        new_local_contents.insert("emptyempty02".into(),
                                  Content::Folder { title: "Empty".into() });
        new_local_contents.insert("emptyemptyL0".into(),
                                  Content::Folder { title: "Empty".into() });

        let remote_tree = nodes!({
            ("mobile______", Folder[needs_merge = true], {
                ("emptyempty01", Folder[needs_merge = true]),
                ("emptyempty02", Folder[needs_merge = true]),
                ("emptyempty03", Folder[needs_merge = true])
            })
        }).into_tree().unwrap();
        let mut new_remote_contents: HashMap<Guid, Content> = HashMap::new();
        new_remote_contents.insert("emptyempty01".into(),
                                   Content::Folder { title: "Empty".into() });
        new_remote_contents.insert("emptyempty02".into(),
                                   Content::Folder { title: "Empty".into() });
        new_remote_contents.insert("emptyempty03".into(),
                                   Content::Folder { title: "Empty".into() });

        let mut merger = Merger::with_contents(&local_tree,
                                               &new_local_contents,
                                               &remote_tree,
                                               &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("mobile______", Folder, {
                ("emptyempty01", Folder),
                ("emptyempty02", Folder),
                ("emptyempty03", Folder)
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts {
            remote_revives: 0,
            local_deletes: 0,
            local_revives: 0,
            remote_deletes: 0,
            dupes: 1,
        };

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    // Bug 747699: we should follow the hierarchy when merging, instead of
    // deduping by parent title.
    #[test]
    fn deduping_ignores_parent_title() {
        before_each();

        let local_tree = nodes!({
            ("mobile______", Folder[needs_merge = true], {
                ("bookmarkAAA1", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        let mut new_local_contents: HashMap<Guid, Content> = HashMap::new();
        new_local_contents.insert("mobile______".into(),
                                  Content::Folder { title: "Favoritos do celular".into() });
        new_local_contents.insert("bookmarkAAA1".into(),
                                  Content::Bookmark { title: "A".into(),
                                                      url_href: "http://example.com/a".into() });

        let remote_tree = nodes!({
            ("mobile______", Folder[needs_merge = true], {
                ("bookmarkAAAA", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        let mut new_remote_contents: HashMap<Guid, Content> = HashMap::new();
        new_remote_contents.insert("mobile______".into(),
                                   Content::Folder { title: "Mobile Bookmarks".into() });
        new_remote_contents.insert("bookmarkAAAA".into(),
                                   Content::Bookmark { title: "A".into(),
                                                       url_href: "http://example.com/a".into() });

        let mut merger = Merger::with_contents(&local_tree,
                                               &new_local_contents,
                                               &remote_tree,
                                               &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("mobile______", Folder, {
                ("bookmarkAAAA", Bookmark)
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts {
            remote_revives: 0,
            local_deletes: 0,
            local_revives: 0,
            remote_deletes: 0,
            dupes: 1,
        };

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn mismatched_compatible_bookmark_kinds() {
        before_each();

        let local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("queryAAAAAAA", Query[needs_merge = true]),
                ("bookmarkBBBB", Bookmark[needs_merge = true, age = 5])
            })
        }).into_tree().unwrap();

        let remote_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("queryAAAAAAA", Bookmark[needs_merge = true, age = 5]),
                ("bookmarkBBBB", Query[needs_merge = true])
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("menu________", Folder, {
                ("queryAAAAAAA", Query),
                ("bookmarkBBBB", Query)
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }

    #[test]
    fn mismatched_incompatible_bookmark_kinds() {
        before_each();

        let local_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkAAAA", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();

        let remote_tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkAAAA", Folder[needs_merge = true, age = 5])
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        match merger.merge() {
            Ok(_) => panic!("Should not merge trees with mismatched kinds"),
            Err(err) => {
                match err.kind() {
                    ErrorKind::MismatchedItemKind { .. } => {},
                    kind => panic!("Got {:?} merging trees with mismatched kinds", kind)
                };
            }
        };
    }

    #[test]
    fn invalid_guids() {
        before_each();

        let local_tree = nodes!({
            ("toolbar_____", Folder[needs_merge = true, age = 5], {
                ("bookmarkAAAA", Bookmark[needs_merge = true, age = 5]),
                ("bookmarkBBBB", Bookmark[needs_merge = true, age = 5])
            }),
            ("menu________", Folder[needs_merge = true], {
                ("shortGUID", Bookmark[needs_merge = true]),
                ("loooooongGUID", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();

        let remote_tree = nodes!({
            ("toolbar_____", Folder[needs_merge = true, age = 5], {
                ("!@#$%^", Bookmark[needs_merge = true, age = 5]),
                ("shortGUID", Bookmark[needs_merge = true, age = 5]),
                ("", Bookmark[needs_merge = true, age = 5]),
                ("loooooongGUID", Bookmark[needs_merge = true, age = 5])
            }),
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkAAAA", Bookmark[needs_merge = true]),
                ("bookmarkBBBB", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();

        let mut merger = Merger::new(&local_tree, &remote_tree);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree = nodes!({
            ("toolbar_____", Folder[needs_merge = true, age = 5], {
                ("!@#$%^", Bookmark[age = 5]),
                ("", Bookmark[age = 5])
            }),
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkAAAA", Bookmark),
                ("bookmarkBBBB", Bookmark),
                ("shortGUID", Bookmark[needs_merge = true]),
                ("loooooongGUID", Bookmark[needs_merge = true])
            })
        }).into_tree().unwrap();
        let expected_telem = StructureCounts::default();

        let merged_tree = merged_root.into_tree().unwrap();
        assert_eq!(merged_tree, expected_tree);

        assert_eq!(merger.deletions().count(), 0);

        assert_eq!(merger.telemetry(), &expected_telem);
    }
}

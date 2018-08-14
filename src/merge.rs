/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{collections::{HashMap, HashSet, VecDeque},
          mem};

use error::{ErrorKind, Result};
use tree::{Content, MergeState, MergedNode, Node, Tree};

const ROOT_GUID: &str = "root________";

static USER_CONTENT_ROOTS: &'static [&'static str] = &["toolbar_____",
                                                       "menu________",
                                                       "unfiled_____",
                                                       "mobile______"];

/// Structure change types, used to indicate if a node on one side is moved
/// or deleted on the other.
#[derive(PartialEq)]
enum StructureChange {
    /// Node not deleted, or doesn't exist, on the other side.
    Unchanged,
    /// Node moved on the other side.
    Moved,
    /// Node deleted on the other side.
    Deleted,
}

#[derive(Default, Debug)]
pub struct StructureCounts {
    new: u64,
    /// Remote non-folder change wins over local deletion.
    remote_revives: u64,
    /// Local folder deletion wins over remote change.
    local_deletes: u64,
    /// Local non-folder change wins over remote deletion.
    local_revives: u64,
    /// Remote folder deletion wins over local change.
    remote_deletes: u64,
}

/// Holds (matching remote dupes for local GUIDs, matching local dupes for
/// remote GUIDs).
type MatchingDupes<'t> = (HashMap<String, Node<'t>>, HashMap<String, Node<'t>>);

/// A two-way merger that produces a complete merged tree from a complete local
/// tree and a complete remote tree with changes since the last sync.
///
/// This is ported almost directly from iOS. On iOS, the `ThreeWayMerger` takes
/// a complete "mirror" tree with the server state after the last sync, and two
/// incomplete trees with local and remote changes to the mirror: "local" and
/// "mirror", respectively. Overlaying buffer onto mirror yields the current
/// server tree; overlaying local onto mirror yields the complete local tree.
///
/// Vellum doesn't store the shared parent for changed items, so we can only
/// do two-way merges. Our local tree is the union of iOS's mirror and local,
/// and our remote tree is the union of iOS's mirror and buffer.
///
/// Unlike iOS, Vellum doesn't distinguish between structure and value changes.
/// The `needs_merge` flag notes *that* a bookmark changed, but not *how*. This
/// means we might detect conflicts, and revert changes on one side, for cases
/// that iOS can merge cleanly.
///
/// Fortunately, most of our users don't organize their bookmarks into deeply
/// nested hierarchies, or make conflicting changes on multiple devices
/// simultaneously. A simpler two-way tree merge strikes a good balance between
/// correctness and complexity.
pub struct Merger<'t> {
    local_tree: &'t Tree,
    new_local_contents: &'t HashMap<String, Content>,
    remote_tree: &'t Tree,
    new_remote_contents: &'t HashMap<String, Content>,
    matching_dupes_by_local_parent_guid: HashMap<String, MatchingDupes<'t>>,
    merged_guids: HashSet<String>,
    delete_locally: HashSet<String>,
    delete_remotely: HashSet<String>,
    structure_counts: StructureCounts,
    dupe_count: u64,
}

impl<'t> Merger<'t> {
    pub fn new(local_tree: &'t Tree,
               new_local_contents: &'t HashMap<String, Content>,
               remote_tree: &'t Tree,
               new_remote_contents: &'t HashMap<String, Content>)
               -> Merger<'t>
    {
        Merger { local_tree,
                 new_local_contents,
                 remote_tree,
                 new_remote_contents,
                 matching_dupes_by_local_parent_guid: HashMap::new(),
                 merged_guids: HashSet::new(),
                 delete_locally: HashSet::new(),
                 delete_remotely: HashSet::new(),
                 structure_counts: StructureCounts::default(),
                 dupe_count: 0, }
    }

    pub fn merge(&mut self) -> Result<MergedNode<'t>> {
        let merged_root_node = {
            let local_root_node = self.local_tree.node_for_guid(ROOT_GUID);
            let remote_root_node = self.remote_tree.node_for_guid(ROOT_GUID);
            self.merge_node(ROOT_GUID, local_root_node, remote_root_node)?
        };

        // Any remaining deletions on one side should be deleted on the other side.
        // This happens when the remote tree has tombstones for items that don't
        // exist locally, or the local tree has tombstones for items that
        // aren't on the server.
        for guid in self.local_tree.deletions() {
            if !self.mentions(guid) {
                self.delete_remotely.insert(guid.to_string());
            }
        }
        for guid in self.remote_tree.deletions() {
            if !self.mentions(guid) {
                self.delete_locally.insert(guid.to_string());
            }
        }

        Ok(merged_root_node)
    }

    pub fn subsumes(&self, tree: &Tree) -> bool {
        tree.guids().iter().all(|guid| self.mentions(guid))
    }

    #[inline]
    fn mentions(&self, guid: &str) -> bool {
        self.merged_guids.contains(guid) ||
        self.delete_locally.contains(guid) ||
        self.delete_remotely.contains(guid)
    }

    /// Merges two nodes, recursively walking folders.
    fn merge_node(&mut self,
                  merged_guid: &str,
                  local_node: Option<Node<'t>>,
                  remote_node: Option<Node<'t>>)
                  -> Result<MergedNode<'t>>
    {
        self.merged_guids.insert(merged_guid.to_string());

        match (local_node, remote_node) {
            (Some(local_node), Some(remote_node)) => {
                trace!("Item {} exists locally as {} and remotely as {}; merging",
                       &merged_guid,
                       local_node,
                       remote_node);
                if local_node.guid != merged_guid {
                    // We deduped a NEW local item to a remote item.
                    self.merged_guids.insert(local_node.guid.to_string());
                }
                let merged_node = self.two_way_merge(merged_guid, local_node, remote_node)?;
                Ok(merged_node)
            },
            (Some(local_node), None) => {
                trace!("Item {} only exists locally as {}; taking local state",
                       merged_guid,
                       local_node);
                if local_node.guid != merged_guid {
                    // We deduped a NEW local item to a remote item.
                    self.merged_guids.insert(local_node.guid.to_string());
                }
                let mut merged_node =
                    MergedNode::new(merged_guid.to_string(), MergeState::local(local_node));
                if local_node.is_folder() {
                    // The local folder doesn't exist remotely, but its children might, so
                    // we still need to recursively walk and merge them. This method will
                    // change the merge state from local to new if any children were moved
                    // or deleted.
                    self.merge_child_lists_into_merged_node(&mut merged_node,
                                                            Some(local_node),
                                                            None)?;
                }
                Ok(merged_node)
            },
            (None, Some(remote_node)) => {
                trace!("Item {} only exists remotely as {}; taking remote state",
                       merged_guid,
                       remote_node);
                let mut merged_node =
                    MergedNode::new(merged_guid.to_string(), MergeState::remote(remote_node));
                if remote_node.is_folder() {
                    // As above, a remote folder's children might still exist locally, so we
                    // need to merge them and update the merge state from remote to new if
                    // any children were moved or deleted.
                    self.merge_child_lists_into_merged_node(&mut merged_node,
                                                            None,
                                                            Some(remote_node))?;
                }
                Ok(merged_node)
            },
            // Should never happen. We need to have at least one node for a two-way
            // merge.
            (None, None) => panic!("Can't merge two nonexistent nodes"),
        }
    }

    /// Merges two nodes that exist locally and remotely.
    fn two_way_merge(&mut self,
                     merged_guid: &str,
                     local_node: Node<'t>,
                     remote_node: Node<'t>)
                     -> Result<MergedNode<'t>>
    {
        let merge_state = self.resolve_two_value_conflict(merged_guid, local_node, remote_node);
        trace!("Merge state for {} is {}", merged_guid, merge_state);

        let mut merged_node = MergedNode::new(merged_guid.to_string(), merge_state);

        if !local_node.has_compatible_kind(&remote_node) {
            error!("Merging local {} and remote {} with different kinds",
                   local_node, remote_node);
            return Err(ErrorKind::ConsistencyError("Can't merge different item kinds").into());
        }

        if local_node.is_folder() && remote_node.is_folder() {
            // Merging two folders, so we need to walk their children to handle
            // structure changes.
            trace!("Merging folders {} and {}", local_node, remote_node);
            self.merge_child_lists_into_merged_node(&mut merged_node,
                                                    Some(local_node),
                                                    Some(remote_node))?;
            return Ok(merged_node);
        }

        // Merging two non-folders, or a local folder and a remote livemark, so
        // there's no need to walk children.
        trace!("Merging non-folders {} and {}", local_node, remote_node);
        Ok(merged_node)
    }

    /// Determines the merge state for a node that exists locally and remotely.
    ///
    /// `merged_guid` is the same as the remote GUID, and usually the same as
    /// the local GUID. The local GUID may be different if we're deduping a
    /// local item to a remote item.
    fn resolve_two_value_conflict(&mut self,
                                  merged_guid: &str,
                                  local_node: Node<'t>,
                                  remote_node: Node<'t>)
                                  -> MergeState<'t>
    {
        if USER_CONTENT_ROOTS.contains(&merged_guid) {
            // Don't update root titles or other properties.
            return MergeState::local(local_node);
        }
        if !remote_node.needs_merge {
            // The node wasn't changed remotely since the last sync. Keep the local
            // state.
            return MergeState::local(remote_node);
        }
        if !local_node.needs_merge {
            // The node was changed remotely, but not locally. Take the remote state.
            return MergeState::remote(remote_node);
        }
        // At this point, we know the item changed locally and remotely. Use the
        // timestamp to decide which node is newer.
        if local_node.newer_than(&remote_node) {
            MergeState::local(local_node)
        } else {
            MergeState::remote(remote_node)
        }
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
                                           -> Result<bool>
    {
        if self.merged_guids.contains(&remote_child_node.guid) {
            trace!("Remote child {} already seen in another folder and merged",
                   remote_child_node);
            return Ok(false);
        }

        trace!("Merging remote child {} of {} into {}",
               remote_child_node,
               remote_parent_node,
               merged_node);

        // Make sure the remote child isn't locally deleted.
        if self.check_for_local_structure_change_of_remote_node(merged_node,
                                                                remote_parent_node,
                                                                remote_child_node)? ==
           StructureChange::Deleted
        {
            // If the remote child is locally deleted, we need to move all descendants
            // that aren't also remotely deleted to the merged node. This handles the
            // case where a user deletes a folder on this device, and adds a bookmark
            // to the same folder on another device. We want to keep the folder
            // deleted, but we also don't want to lose the new bookmark, so we move
            // the bookmark to the deleted folder's parent.
            return Ok(true);
        }

        // The remote child isn't locally deleted. Does it exist in the local tree?
        if let Some(local_child_node) = self.local_tree.node_for_guid(&remote_child_node.guid) {
            // Otherwise, the remote child exists in the local tree. Did it move?
            let local_parent_node =
                local_child_node.parent()
                                .expect("Can't merge existing remote child without local parent");

            trace!("Remote child {} exists locally in {} and remotely in {}",
                   remote_child_node,
                   local_parent_node,
                   remote_parent_node);

            if self.remote_tree.is_deleted(&local_parent_node.guid) {
                trace!("Unconditionally taking remote move for {} to {} because local parent {} \
                        is deleted remotely",
                       remote_child_node,
                       remote_parent_node,
                       local_parent_node);

                let merged_child_node = self.merge_node(&local_child_node.guid,
                                                        Some(local_child_node),
                                                        Some(remote_child_node))?;
                merged_node.merged_children.push(merged_child_node);
                return Ok(false);
            }

            match (local_parent_node.needs_merge, remote_parent_node.needs_merge) {
                (true, true) => {
                    trace!("Local {} and remote {} parents changed; comparing modified times to \
                            decide parent for remote child {}",
                           local_parent_node,
                           remote_parent_node,
                           remote_child_node);

                    let latest_local_age = local_child_node.age.min(local_parent_node.age);
                    let latest_remote_age = remote_child_node.age.min(remote_parent_node.age);

                    if latest_local_age < latest_remote_age {
                        // Local move is younger, so we ignore the remote move. We'll
                        // merge the child later, when we walk its new local parent.
                        trace!("Ignoring older remote move for {} to {} at {}; local move to {} \
                                at {} is newer",
                               remote_child_node,
                               remote_parent_node,
                               latest_remote_age,
                               local_parent_node,
                               latest_local_age);
                        return Ok(true);
                    }

                    // Otherwise, the remote move is younger, so we ignore the local move
                    // and merge the child now.
                    trace!("Taking newer remote move for {} to {} at {}; local move to {} at {} \
                            is older",
                           remote_child_node,
                           remote_parent_node,
                           latest_remote_age,
                           local_parent_node,
                           latest_local_age);

                    let merged_child_node = self.merge_node(&remote_child_node.guid,
                                                            Some(local_child_node),
                                                            Some(remote_child_node))?;
                    merged_node.merged_children.push(merged_child_node);
                    return Ok(false);
                },

                (true, false) => {
                    trace!("Remote parent unchanged; keeping remote child {} in {}",
                           remote_child_node,
                           local_parent_node);
                    return Ok(true);
                },

                (false, _) => {
                    trace!("Local parent unchanged; keeping remote child {} in {}",
                           remote_child_node,
                           remote_parent_node);
                    let merged_child_node = self.merge_node(&remote_child_node.guid,
                                                            Some(local_child_node),
                                                            Some(remote_child_node))?;
                    merged_node.merged_children.push(merged_child_node);
                    return Ok(false);
                },
            }
        } else {
            // Remote child is not a root, and doesn't exist locally. Try to find a
            // content match in the containing folder, and dedupe the local item if
            // we can.
            trace!("Remote child {} doesn't exist locally; looking for local content match",
                   remote_child_node);
            let local_child_node_by_content =
                self.find_local_node_matching_remote_node(merged_node,
                                                          local_parent_node,
                                                          remote_parent_node,
                                                          remote_child_node);
            let merged_child_node = self.merge_node(&remote_child_node.guid,
                                                    local_child_node_by_content,
                                                    Some(remote_child_node))?;
            merged_node.merged_children.push(merged_child_node);
            return Ok(false);
        }
    }

    /// Merges a local child node into a merged folder node.
    ///
    /// This is the inverse of `merge_remote_child_into_merged_node`.
    ///
    /// Returns `true` if the merged structure state changed because the local
    /// child doesn't exist remotely or was locally moved; `false` otherwise.
    ///
    fn merge_local_child_into_merged_node(&mut self,
                                          merged_node: &mut MergedNode<'t>,
                                          local_parent_node: Node<'t>,
                                          remote_parent_node: Option<Node<'t>>,
                                          local_child_node: Node<'t>)
                                          -> Result<bool>
    {
        if self.merged_guids.contains(&local_child_node.guid) {
            // We already merged the child when we walked another folder.
            trace!("Local child {} already seen in another folder and merged",
                   local_child_node);
            return Ok(false);
        }

        trace!("Merging local child {} of {} into {}",
               local_child_node,
               local_parent_node,
               merged_node);

        // Now, we know we haven't seen the local child before, and it's not in
        // this folder on the server. Check if the child is remotely deleted.
        if self.check_for_remote_structure_change_of_local_node(merged_node,
                                                                local_parent_node,
                                                                local_child_node)? ==
           StructureChange::Deleted
        {
            // If the child is remotely deleted, we need to move any new local
            // descendants to the merged node, just as we did for new remote
            // descendants of locally deleted children.
            return Ok(true);
        }

        // At this point, we know the local child isn't deleted. See if it
        // exists in the remote tree.
        if let Some(remote_child_node) = self.remote_tree.node_for_guid(&local_child_node.guid) {
            // The local child exists remotely. It must have moved; otherwise, we
            // would have seen it when we walked the remote children.
            let remote_parent_node =
                remote_child_node.parent()
                                 .expect("Can't merge existing local child without remote parent");

            trace!("Local child {} exists locally in {} and remotely in {}",
                   local_child_node,
                   local_parent_node,
                   remote_parent_node);

            if self.local_tree.is_deleted(&remote_parent_node.guid) {
                trace!("Unconditionally taking local move for {} to {} because remote parent {} \
                        is deleted locally",
                       local_child_node,
                       local_parent_node,
                       remote_parent_node);

                let merged_child_node = self.merge_node(&local_child_node.guid,
                                                        Some(local_child_node),
                                                        Some(remote_child_node))?;
                merged_node.merged_children.push(merged_child_node);
                return Ok(true);
            }

            match (local_parent_node.needs_merge, remote_parent_node.needs_merge) {
                (true, true) => {
                    trace!("Local {} and remote {} parents changed; comparing modified times to \
                            decide parent for local child {}",
                           local_parent_node,
                           remote_parent_node,
                           local_child_node);

                    let latest_local_age = local_child_node.age.min(local_parent_node.age);
                    let latest_remote_age = remote_child_node.age.min(remote_parent_node.age);

                    if latest_remote_age <= latest_local_age {
                        trace!("Ignoring older local move for {} to {} at {}; remote move to {} \
                                at {} is newer",
                               local_child_node,
                               local_parent_node,
                               latest_local_age,
                               remote_parent_node,
                               latest_remote_age);
                        return Ok(false);
                    }

                    trace!("Taking newer local move for {} to {} at {}; remote move to {} at {} \
                            is older",
                           local_child_node,
                           local_parent_node,
                           latest_local_age,
                           remote_parent_node,
                           latest_remote_age);

                    let merged_child_node = self.merge_node(&local_child_node.guid,
                                                            Some(local_child_node),
                                                            Some(remote_child_node))?;
                    merged_node.merged_children.push(merged_child_node);
                    return Ok(true);
                },
                (true, false) => {
                    trace!("Remote parent unchanged; keeping local child {} in local parent {}",
                           local_child_node,
                           local_parent_node);

                    let merged_child_node = self.merge_node(&local_child_node.guid,
                                                            Some(local_child_node),
                                                            Some(remote_child_node))?;
                    merged_node.merged_children.push(merged_child_node);
                    return Ok(true);
                },
                (false, _) => {
                    trace!("Local parent unchanged; keeping local child {} in remote parent {}",
                           local_child_node,
                           remote_parent_node);
                    return Ok(false);
                },
            }
        } else {
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
                let merged_child_node = self.merge_node(&remote_child_node_by_content.guid,
                                                        Some(local_child_node),
                                                        Some(remote_child_node_by_content))?;
                merged_node.merged_children.push(merged_child_node);
                return Ok(false);
            } else {
                // The local child doesn't exist remotely, but we still need to walk
                // its children.
                let merged_child_node =
                    self.merge_node(&local_child_node.guid, Some(local_child_node), None)?;
                merged_node.merged_children.push(merged_child_node);
                return Ok(true);
            }
        }
    }

    /// Recursively merges the children of a local folder node and a matching
    /// remote folder node.
    ///
    /// This method mutates the merged node to append local and remote
    /// children, and sets a new merge state state if needed.
    fn merge_child_lists_into_merged_node(&mut self,
                                          merged_node: &mut MergedNode<'t>,
                                          local_node: Option<Node<'t>>,
                                          remote_node: Option<Node<'t>>)
                                          -> Result<()>
    {
        let merge_state_changed = match (local_node, remote_node) {
            (Some(local_node), Some(remote_node)) => {
                if local_node.newer_than(&remote_node) {
                    // The folder exists locally and remotely, and the local node is newer.
                    // Walk and merge local children first, followed by remaining unmerged
                    // remote children.
                    let local_merge_state_changed =
                        self.merge_local_children_into_merged_node(merged_node,
                                                                   local_node,
                                                                   Some(remote_node))?;
                    let remote_merge_state_changed =
                        self.merge_remote_children_into_merged_node(merged_node,
                                                                    Some(local_node),
                                                                    remote_node)?;
                    local_merge_state_changed || remote_merge_state_changed
                } else {
                    // The folder exists locally and remotely, and the remote node is newer.
                    // Merge remote children first, then remaining local children.
                    let remote_merge_state_changed =
                        self.merge_remote_children_into_merged_node(merged_node,
                                                                    Some(local_node),
                                                                    remote_node)?;
                    let local_merge_state_changed =
                        self.merge_local_children_into_merged_node(merged_node,
                                                                   local_node,
                                                                   Some(remote_node))?;
                    remote_merge_state_changed || local_merge_state_changed
                }
            },
            (Some(local_node), None) => {
                // The folder only exists locally, so no remote children to merge.
                self.merge_local_children_into_merged_node(merged_node, local_node, None)?
            },
            (None, Some(remote_node)) => {
                // The folder only exists remotely, so local children to merge.
                self.merge_remote_children_into_merged_node(merged_node, None, remote_node)?
            },
            (None, None) => panic!("Can't merge children for two nonexistent nodes"),
        };

        // Update the merge state if we moved children orphaned on one side by a
        // deletion on the other side, if we kept newer locally moved children,
        // or if the child order changed. We already updated the merge state of the
        // orphans, but we also need to flag the containing folder so that it's
        // reuploaded to the server along with the new children.
        if merge_state_changed {
            let new_merge_state = MergeState::new(merged_node.merge_state);
            trace!("Merge state for {} has new structure {}",
                   merged_node,
                   new_merge_state);
            self.structure_counts.new += 1;
            merged_node.merge_state = new_merge_state;
        }

        Ok(())
    }

    /// Recursively merges the children of a remote folder node.
    ///
    /// Returns `true` if the merge produced a new structure that should be
    /// reuploaded to the server; `false` otherwise.
    fn merge_remote_children_into_merged_node(&mut self,
                                              merged_node: &mut MergedNode<'t>,
                                              local_node: Option<Node<'t>>,
                                              remote_node: Node<'t>)
                                              -> Result<bool>
    {
        trace!("Merging remote children of {} into {}",
               remote_node,
               merged_node);

        let mut merge_state_changed = false;
        for remote_child_node in remote_node.children() {
            let remote_children_changed =
                self.merge_remote_child_into_merged_node(merged_node,
                                                         local_node,
                                                         remote_node,
                                                         remote_child_node)?;
            if remote_children_changed {
                merge_state_changed = true;
            }
        }

        Ok(merge_state_changed)
    }

    /// Recursively merges the children of a local folder node.
    ///
    /// Returns `true` if the merge produced a new structure that should be
    /// reuploaded to the server; `false` otherwise.
    fn merge_local_children_into_merged_node(&mut self,
                                             merged_node: &mut MergedNode<'t>,
                                             local_node: Node<'t>,
                                             remote_node: Option<Node<'t>>)
                                             -> Result<bool>
    {
        trace!("Merging local children of {} into {}",
               local_node,
               merged_node);

        let mut merge_state_changed = false;
        for local_child_node in local_node.children() {
            let remote_children_changed =
                self.merge_local_child_into_merged_node(merged_node,
                                                        local_node,
                                                        remote_node,
                                                        local_child_node)?;
            if remote_children_changed {
                merge_state_changed = true;
            }
        }

        Ok(merge_state_changed)
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
        if !remote_node.is_syncable {
            // If the remote node is known to be non-syncable, we unconditionally
            // delete it from the server, even if it's syncable locally.
            self.delete_remotely.insert(remote_node.guid.to_string());
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
                if !local_node.is_syncable {
                    // The remote node is syncable, but the local node is non-syncable.
                    // For consistency with Desktop, we unconditionally delete the
                    // node from the server.
                    self.delete_remotely.insert(remote_node.guid.to_string());
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
        self.delete_remotely.insert(remote_node.guid.to_string());
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
        if !local_node.is_syncable {
            // If the local node is known to be non-syncable, we unconditionally
            // delete it from the local tree, even if it's syncable remotely.
            self.delete_locally.insert(local_node.guid.to_string());
            if local_node.is_folder() {
                self.relocate_local_orphans_to_merged_node(merged_node, local_node)?;
            }
            return Ok(StructureChange::Deleted);
        }

        if !self.remote_tree.is_deleted(&local_node.guid) {
            if let Some(remote_node) = self.remote_tree.node_for_guid(&local_node.guid) {
                if !remote_node.is_syncable {
                    // The local node is syncable, but the remote node is non-syncable.
                    // This can happen if we applied an orphaned left pane query in a
                    // previous sync, and later saw the left pane root on the server.
                    // Since we now have the complete subtree, we can remove the item.
                    self.delete_locally.insert(local_node.guid.to_string());
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
        self.delete_locally.insert(local_node.guid.to_string());
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
                    let local_child_node = self.local_tree.node_for_guid(&remote_child_node.guid);
                    let mut merged_orphan_node = self.merge_node(&remote_child_node.guid,
                                                                 local_child_node,
                                                                 Some(remote_child_node))?;

                    // Flag the moved orphan for reupload.
                    let merge_state = MergeState::new(merged_orphan_node.merge_state);
                    merged_orphan_node.merge_state = merge_state;
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
                    let remote_child_node = self.remote_tree.node_for_guid(&local_child_node.guid);
                    let mut merged_orphan_node = self.merge_node(&local_child_node.guid,
                                                                 Some(local_child_node),
                                                                 remote_child_node)?;

                    let merge_state = MergeState::new(merged_orphan_node.merge_state);
                    merged_orphan_node.merge_state = merge_state;
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
            if let Some(local_child_content) = self.new_local_contents.get(&local_child_node.guid) {
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
                self.new_remote_contents.get(&remote_child_node.guid)
            {
                if let Some(mut local_nodes_for_key) =
                    dupe_key_to_local_nodes.get_mut(remote_child_content)
                {
                    if let Some(local_child_node) = local_nodes_for_key.pop_front() {
                        trace!("Deduping local child {} to remote child {}",
                               local_child_node,
                               remote_child_node);
                        local_to_remote.insert(local_child_node.guid.to_string(),
                                               remote_child_node);
                        remote_to_local.insert(remote_child_node.guid.to_string(),
                                               local_child_node);
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
                    .entry(local_parent_node.guid.to_string())
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
                                            self.dupe_count += 1;
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
                    .entry(local_parent_node.guid.to_string())
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
                                           self.dupe_count += 1;
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
    use tree::{Item, Kind};

    #[derive(Debug)]
    struct Node {
        item: Item,
        children: Vec<Box<Node>>,
    }

    impl Into<Tree> for Node {
        fn into(self) -> Tree {
            fn inflate(tree: &mut Tree, parent_guid: &str, node: Node) {
                let guid = node.item.guid.clone();
                tree.insert(parent_guid, node.item);
                node.children
                    .into_iter()
                    .for_each(|child| inflate(tree, &guid, *child))
            }

            let guid = self.item.guid.clone();
            let mut tree = Tree::new(self.item);
            self.children
                .into_iter()
                .for_each(|child| inflate(&mut tree, &guid, *child));
            tree
        }
    }

    macro_rules! nodes {
        ($children:tt) => { nodes!(ROOT_GUID, Folder, $children) };
        ($guid:expr, $kind:ident) => { nodes!($guid, $kind[]) };
        ($guid:expr, $kind:ident [ $( $name:ident = $value:expr ),* ]) => {{
            let mut item = Item::new($guid, Kind::$kind);
            $({ item.$name = $value; })*
            Node { item, children: Vec::new() }
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

        let local_tree: Tree = nodes!({
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
        }).into();
        let new_local_contents = HashMap::new();

        let remote_tree: Tree = nodes!({
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
        }).into();
        let new_remote_contents = HashMap::new();

        let mut merger = Merger::new(&local_tree,
                                     &new_local_contents,
                                     &remote_tree,
                                     &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree: Tree = nodes!({
            ("unfiled_____", Folder, {
                ("folderBBBBBB", Folder, {
                    ("bookmarkDDDD", Bookmark),
                    ("bookmarkAAAA", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                })
            }),
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkEEEE", Bookmark)
                })
            }),
            ("menu________", Folder, {
                ("bookmarkFFFF", Bookmark)
            })
        }).into();
        let merged_tree: Tree = merged_root.into();
        assert_eq!(merged_tree, expected_tree);
    }

    // This test moves a bookmark that exists locally into a new folder that only
    // exists remotely, and is a later sibling of the local parent.
    #[test]
    fn move_into_parent_sibling() {
        before_each();

        let local_tree: Tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("folderAAAAAA", Folder[needs_merge = true], {
                    ("bookmarkBBBB", Bookmark[needs_merge = true])
                })
            })
        }).into();
        let new_local_contents = HashMap::new();

        let remote_tree: Tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("folderAAAAAA", Folder[needs_merge = true]),
                ("folderCCCCCC", Folder[needs_merge = true], {
                    ("bookmarkBBBB", Bookmark[needs_merge = true])
                })
            })
        }).into();
        let new_remote_contents = HashMap::new();

        let mut merger = Merger::new(&local_tree,
                                     &new_local_contents,
                                     &remote_tree,
                                     &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder),
                ("folderCCCCCC", Folder, {
                    ("bookmarkBBBB", Bookmark)
                })
            })
        }).into();
        let merged_tree: Tree = merged_root.into();
        assert_eq!(merged_tree, expected_tree);
    }

    #[test]
    fn reorder_and_insert() {
        before_each();

        let shared_tree: Tree = nodes!({
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
        }).into();

        let local_tree: Tree = nodes!({
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
        }).into();
        let new_local_contents = HashMap::new();

        let remote_tree: Tree = nodes!({
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
        }).into();
        let new_remote_contents = HashMap::new();

        let mut merger = Merger::new(&local_tree,
                                     &new_local_contents,
                                     &remote_tree,
                                     &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree: Tree = nodes!({
            ("menu________", Folder, {
                // The server has an older menu, so we should use the local order (C A B)
                // as the base, then append (I J).
                ("bookmarkCCCC", Bookmark[age = 5]),
                ("bookmarkAAAA", Bookmark[age = 5]),
                ("bookmarkBBBB", Bookmark[age = 5]),
                ("bookmarkIIII", Bookmark),
                ("bookmarkJJJJ", Bookmark)
            }),
            ("toolbar_____", Folder[age = 5], {
                // The server has a newer toolbar, so we should use the remote order (F D E)
                // as the base, then append (G H).
                ("bookmarkFFFF", Bookmark),
                ("bookmarkDDDD", Bookmark),
                ("bookmarkEEEE", Bookmark),
                ("bookmarkGGGG", Bookmark),
                ("bookmarkHHHH", Bookmark)
            })
        }).into();
        let merged_tree: Tree = merged_root.into();
        assert_eq!(merged_tree, expected_tree);
    }

    #[test]
    fn value_structure_conflict() {
        before_each();

        let shared_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                }),
                ("folderDDDDDD", Folder, {
                    ("bookmarkEEEE", Bookmark)
                })
            })
        }).into();

        let local_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder[needs_merge = true, age = 10], {
                    ("bookmarkCCCC", Bookmark)
                }),
                ("folderDDDDDD", Folder[needs_merge = true, age = 10], {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkEEEE", Bookmark[age = 10])
                })
            })
        }).into();
        let new_local_contents = HashMap::new();

        let remote_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                }),
                ("folderDDDDDD", Folder[needs_merge = true, age = 5], {
                    ("bookmarkEEEE", Bookmark[needs_merge = true, age = 5])
                })
            })
        }).into();
        let new_remote_contents = HashMap::new();

        let mut merger = Merger::new(&local_tree,
                                     &new_local_contents,
                                     &remote_tree,
                                     &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkCCCC", Bookmark)
                }),
                ("folderDDDDDD", Folder[age = 5], {
                    ("bookmarkEEEE", Bookmark[age = 5]),
                    ("bookmarkBBBB", Bookmark)
                })
            })
        }).into();
        let merged_tree: Tree = merged_root.into();
        assert_eq!(merged_tree, expected_tree);
    }

    #[test]
    fn complex_move_with_additions() {
        before_each();

        let shared_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark)
                })
            })
        }).into();

        let local_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkCCCC", Bookmark),
                    ("bookmarkDDDD", Bookmark)
                })
            })
        }).into();
        let new_local_contents = HashMap::new();

        let remote_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("bookmarkCCCC", Bookmark)
            }),
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder, {
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkEEEE", Bookmark)
                })
            })
        }).into();
        let new_remote_contents = HashMap::new();

        let mut merger = Merger::new(&local_tree,
                                     &new_local_contents,
                                     &remote_tree,
                                     &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("bookmarkCCCC", Bookmark)
            }),
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder, {
                    // We can guarantee child order (B E D), since we always walk remote
                    // children first, and the remote folder A record is newer than the
                    // local folder. If the local folder were newer, the order would be
                    // (D B E).
                    ("bookmarkBBBB", Bookmark),
                    ("bookmarkEEEE", Bookmark),
                    ("bookmarkDDDD", Bookmark)
                })
            })
        }).into();
        let merged_tree: Tree = merged_root.into();
        assert_eq!(merged_tree, expected_tree);
    }

    #[test]
    fn complex_orphaning() {
        before_each();

        let shared_tree: Tree = nodes!({
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
        }).into();

        // Locally: delete E, add B > F.
        let mut local_tree: Tree = nodes!({
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
        }).into();
        local_tree.note_deleted("folderEEEEEE");
        let new_local_contents = HashMap::new();

        // Remotely: delete B, add E > G.
        let mut remote_tree: Tree = nodes!({
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
        }).into();
        remote_tree.note_deleted("folderBBBBBB");
        let new_remote_contents = HashMap::new();

        let mut merger = Merger::new(&local_tree,
                                     &new_local_contents,
                                     &remote_tree,
                                     &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree: Tree = nodes!({
            ("toolbar_____", Folder, {
                ("folderAAAAAA", Folder, {
                    // B was deleted remotely, so F moved to A, the closest
                    // surviving parent.
                    ("bookmarkFFFF", Bookmark)
                })
            }),
            ("menu________", Folder, {
                ("folderCCCCCC", Folder, {
                    ("folderDDDDDD", Folder, {
                        // E was deleted locally, so G moved to D.
                        ("bookmarkGGGG", Bookmark)
                    })
                })
            })
        }).into();
        let merged_tree: Tree = merged_root.into();
        assert_eq!(merged_tree, expected_tree);
    }

    #[test]
    fn duping_local_newer() {
        before_each();

        let local_tree: Tree = nodes!({
            ("menu________", Folder[needs_merge = true], {
                ("bookmarkAAA1", Bookmark[needs_merge = true]),
                ("bookmarkAAA2", Bookmark[needs_merge = true]),
                ("bookmarkAAA3", Bookmark[needs_merge = true])
            })
        }).into();
        let mut new_local_contents: HashMap<String, Content> = HashMap::new();
        new_local_contents.insert("bookmarkAAA1".into(),
                                  Content::Bookmark { title: "A".into(),
                                                      url_href: "http://example.com/a".into(), });
        new_local_contents.insert("bookmarkAAA2".into(),
                                  Content::Bookmark { title: "A".into(),
                                                      url_href: "http://example.com/a".into(), });
        new_local_contents.insert("bookmarkAAA3".into(),
                                  Content::Bookmark { title: "A".into(),
                                                      url_href: "http://example.com/a".into(), });

        let remote_tree: Tree = nodes!({
            ("menu________", Folder[needs_merge = true, age = 5], {
                ("bookmarkAAAA", Bookmark[needs_merge = true, age = 5]),
                ("bookmarkAAA4", Bookmark[needs_merge = true, age = 5]),
                ("bookmarkAAA5", Bookmark)
            })
        }).into();
        let mut new_remote_contents: HashMap<String, Content> = HashMap::new();
        new_remote_contents.insert("bookmarkAAAA".into(),
                                   Content::Bookmark { title: "A".into(),
                                                       url_href: "http://example.com/a".into(), });
        new_remote_contents.insert("bookmarkAAA4".into(),
                                   Content::Bookmark { title: "A".into(),
                                                       url_href: "http://example.com/a".into(), });

        let mut merger = Merger::new(&local_tree,
                                     &new_local_contents,
                                     &remote_tree,
                                     &new_remote_contents);
        let merged_root = merger.merge().unwrap();
        assert!(merger.subsumes(&local_tree));
        assert!(merger.subsumes(&remote_tree));

        let expected_tree: Tree = nodes!({
            ("menu________", Folder, {
                ("bookmarkAAAA", Bookmark),
                ("bookmarkAAA4", Bookmark),
                ("bookmarkAAA3", Bookmark),
                ("bookmarkAAA5", Bookmark)
            })
        }).into();
        let merged_tree: Tree = merged_root.into();
        assert_eq!(merged_tree, expected_tree);
    }
}

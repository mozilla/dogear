// Copyright 2018-2019 Mozilla

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

use std::{collections::HashMap, time::Duration};

use crate::driver::{DefaultDriver, Driver};
use crate::error::{Error, ErrorKind};
use crate::guid::Guid;
use crate::merge::{Merger, Deletion, StructureCounts};
use crate::tree::{Content, MergedDescendant, Tree};

/// Records timings and counters for telemetry.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Stats {
    pub timings: MergeTimings,
    pub counts: StructureCounts,
}

/// Records timings for merging operations.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MergeTimings {
    pub fetch_local_tree: Duration,
    pub fetch_new_local_contents: Duration,
    pub fetch_remote_tree: Duration,
    pub fetch_new_remote_contents: Duration,
    pub merge: Duration,
    pub apply: Duration,
}

#[macro_export]
macro_rules! time {
    ($timings:ident, $name:ident, $op:expr) => {{
        let now = std::time::Instant::now();
        let result = $op;
        $timings.$name = now.elapsed();
        result
    }};
}

pub trait Store<E: From<Error>> {
    /// Builds a fully rooted, consistent tree from the items and tombstones in
    /// the local store.
    fn fetch_local_tree(&self) -> Result<Tree, E>;

    /// Fetches content info for all new local items that haven't been uploaded
    /// or merged yet. We'll try to dedupe them to remotely changed items with
    /// similar contents and different GUIDs.
    fn fetch_new_local_contents(&self) -> Result<HashMap<Guid, Content>, E>;

    /// Builds a fully rooted, consistent tree from the items and tombstones in
    /// the mirror.
    fn fetch_remote_tree(&self) -> Result<Tree, E>;

    /// Fetches content info for all items in the mirror that changed since the
    /// last sync and don't exist locally. We'll try to match new local items to
    /// these.
    fn fetch_new_remote_contents(&self) -> Result<HashMap<Guid, Content>, E>;

    /// Applies the merged tree and stages items to upload. We keep this
    /// generic: on Desktop, we'll insert the merged tree into a temp
    /// table, update Places, and stage outgoing items in another temp
    /// table. Afterward, we can inflate records on the JS side. On mobile,
    /// this flow might be simpler.
    fn apply<'t>(&self, descendants: Vec<MergedDescendant<'t>>,
                 deletions: Vec<Deletion>) -> Result<(), E>;

    /// Builds and applies a merged tree using the default merge driver.
    fn merge(&self) -> Result<Stats, E> {
        self.merge_with_driver(&DefaultDriver)
    }

    /// Builds a complete merged tree from the local and remote trees, resolves
    /// conflicts, dedupes local items, and applies the merged tree using the
    /// given driver.
    fn merge_with_driver<D: Driver>(&self, driver: &D) -> Result<Stats, E> {
        let mut merge_timings = MergeTimings::default();
        let local_tree = time!(merge_timings, fetch_local_tree, {
            self.fetch_local_tree()
        })?;
        debug!(driver, "Built local tree from mirror\n{}", local_tree);

        let new_local_contents = time!(merge_timings, fetch_new_local_contents, {
            self.fetch_new_local_contents()
        })?;

        let remote_tree = time!(merge_timings, fetch_remote_tree, {
            self.fetch_remote_tree()
        })?;
        debug!(driver, "Built remote tree from mirror\n{}", remote_tree);

        let new_remote_contents = time!(merge_timings, fetch_new_remote_contents, {
            self.fetch_new_remote_contents()
        })?;

        let mut merger = Merger::with_driver(driver, &local_tree,
                                             &new_local_contents, &remote_tree,
                                             &new_remote_contents);
        let merged_root = time!(merge_timings, merge, merger.merge())?;
        debug!(driver, "Built new merged tree\n{}\nDelete Locally: [{}]\nDelete Remotely: [{}]",
               merged_root.to_ascii_string(),
               merger.delete_locally.iter().map(Guid::as_str).collect::<Vec<_>>().join(", "),
               merger.delete_remotely.iter().map(Guid::as_str).collect::<Vec<_>>().join(", "));

        if !merger.subsumes(&local_tree) {
            Err(E::from(ErrorKind::UnmergedLocalItems.into()))?;
        }
        if !merger.subsumes(&remote_tree) {
            Err(E::from(ErrorKind::UnmergedRemoteItems.into()))?;
        }

        let descendants = merged_root.descendants_with_size_hint(
            Some(merger.structure_counts.merged_nodes));
        let deletions = merger.deletions().collect::<Vec<_>>();
        time!(merge_timings, apply, self.apply(descendants, deletions))?;

        Ok(Stats { timings: merge_timings, counts: merger.structure_counts.clone() })
    }
}

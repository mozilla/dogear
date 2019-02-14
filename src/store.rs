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

use std::collections::HashMap;

use crate::driver::{LogLevel, Driver, Stats, Timing, Counter};
use crate::error::{Error, ErrorKind};
use crate::guid::Guid;
use crate::merge::{Merger, Deletion};
use crate::tree::{Content, MergedDescendant, Tree};

pub trait Store<D: Driver, E: From<Error>> {
    /// Builds a fully rooted, consistent tree from the items and tombstones in
    /// the local store.
    fn fetch_local_tree(&self, local_time_millis: i64) -> Result<Tree, E>;

    /// Fetches content info for all new local items that haven't been uploaded
    /// or merged yet. We'll try to dedupe them to remotely changed items with
    /// similar contents and different GUIDs.
    fn fetch_new_local_contents(&self) -> Result<HashMap<Guid, Content>, E>;

    /// Builds a fully rooted, consistent tree from the items and tombstones in
    /// the mirror.
    fn fetch_remote_tree(&self, remote_time_millis: i64) -> Result<Tree, E>;

    /// Fetches content info for all items in the mirror that changed since the
    /// last sync and don't exist locally. We'll try to match new local items to
    /// these.
    fn fetch_new_remote_contents(&self) -> Result<HashMap<Guid, Content>, E>;

    /// Applies the merged tree and stages items to upload. We keep this
    /// generic: on Desktop, we'll insert the merged tree into a temp
    /// table, update Places, and stage outgoing items in another temp
    /// table. Afterward, we can inflate records on the JS side. On mobile,
    /// this flow might be simpler.
    fn apply<'t>(&mut self, descendants: Vec<MergedDescendant<'t>>,
                 deletions: Vec<Deletion>) -> Result<(), E>;

    fn merge(&mut self, driver: &D, stats: &mut Stats, local_time_millis: i64,
             remote_time_millis: i64) -> Result<(), E> {

        let local_tree = stats
            .time(Timing::FetchLocalTree)
            .record(|| self.fetch_local_tree(local_time_millis))?;
        trace!(driver, "Built local tree from mirror\n{}", local_tree);

        let new_local_contents = stats
            .time(Timing::FetchNewLocalContents)
            .record(|| self.fetch_new_local_contents())?;

        let remote_tree = stats
            .time(Timing::FetchRemoteTree)
            .record(|| self.fetch_remote_tree(remote_time_millis))?;
        trace!(driver, "Built remote tree from mirror\n{}", remote_tree);

        let new_remote_contents = stats
            .time(Timing::FetchNewRemoteContents)
            .record(|| self.fetch_new_remote_contents())?;

        let mut merger = Merger::with_driver(driver, &local_tree, &new_local_contents,
                                             &remote_tree, &new_remote_contents);
        let merged_root = stats.time(Timing::Merge).record(|| merger.merge())?;
        if driver.log_level() >= LogLevel::Trace {
            let delete_locally = merger
                .delete_locally
                .iter()
                .map(|guid| guid.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            let delete_remotely = merger
                .delete_remotely
                .iter()
                .map(|guid| guid.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            trace!(driver, "Built new merged tree\n{}\nDelete Locally: [{}]\nDelete Remotely: [{}]",
                   merged_root.to_ascii_string(), delete_locally, delete_remotely);
        }
        stats
            .count(Counter::RemoteRevives)
            .set(merger.structure_counts.remote_revives)
            .count(Counter::LocalDeletes)
            .set(merger.structure_counts.local_deletes)
            .count(Counter::LocalRevives)
            .set(merger.structure_counts.local_revives)
            .count(Counter::RemoteDeletes)
            .set(merger.structure_counts.remote_deletes)
            .count(Counter::Dupes)
            .set(merger.structure_counts.dupes);

        if !merger.subsumes(&local_tree) {
            Err(E::from(ErrorKind::UnmergedLocalItems.into()))?;
        }
        if !merger.subsumes(&remote_tree) {
            Err(E::from(ErrorKind::UnmergedRemoteItems.into()))?;
        }

        let descendants = merged_root.descendants();
        let deletions = merger.deletions().collect::<Vec<_>>();
        stats
            .count(Counter::MergedNodes)
            .set(descendants.len() as i64)
            .count(Counter::MergedDeletions)
            .set(deletions.len() as i64);
        stats
            .time(Timing::Apply)
            .record(|| self.apply(descendants, deletions))?;

        Ok(())
    }
}

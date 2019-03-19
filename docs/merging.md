# Merging

Dogear's `Merger` produces a complete, consistent merged tree from a local and remote bookmark tree. The merge algorithm examines each item, and resolves two kinds of changes:

* **Structure changes** to an item's parent or children, like adding or deleting an item, moving an item to a different folder, or reordering a folder's children.
* **Value changes** to an item's properties, like the title or URL.

## Merge states

Each merged item has a merge state that describes how to resolve the change. The merge state determines:

* Which side—local or remote—to prefer when resolving a conflict.
* Whether or not to **apply** a remote change to the local tree.
* Whether or not to **upload** the merged item to the server.

There are seven merge states:

* Items that are unchanged (`MergeState::Unchanged`) on both sides don't need to be uploaded or applied.
* Items that only exist remotely (`MergeState::RemoteOnly`), only changed remotely, or have newer remote changes (`MergeState::Remote`), must be applied to the local tree. This overwrites any local changes to the item.
* Items that only exist remotely (`MergeState::RemoteOnlyWithNewStructure`) or have newer remote changes (`MergeState::RemoteWithNewStructure`), but _conflict_ with local structure changes, must be applied to the local tree _and_ reuploaded to the server. This resolves the conflict on both sides.
* Items that only exist locally (`MergeState::LocalOnly`), only changed locally, or have newer local changes (`MergeState::Local`), must be uploaded to the server. This overwrites remote changes to the item. Since `LocalOnly` and `Local` always imply upload, there are no corresponding `WithNewStructure` states.

The merger starts at the roots of both trees, and recursively walks their children, eventually visiting every item.

## Conflicts

Structure and value conflicts, where an item changes on both sides, are resolved using timestamps, picking the chronologically newer side. The merger handles conflicts at the _item_ level, not the _property_ level, using the `needs_merge` flag.

For example, consider changing a bookmark's title locally, and the same bookmark's URL remotely. Both items have `needs_merge = true` set.

* If the local title change is newer (`local_item.age < remote_item.age`), the URL change will be reverted on the server.
* If the remote URL change is newer (`remote_item.age > local_item.age`), the title change will be reverted locally.

Since the only indication that an item changed is its `needs_merge` flag, and there's no shared parent tree, Dogear can't know which fields changed, or if they're independent. In other words, the merger knows _that_ the item changed, but not _how_. For this reason, the algorithm is a **two-way merge**, not a three-way merge.

This is a trade-off between simplicity and correctness: it removes a chunk of complexity from Dogear, and means that clients don't need to persist snapshots of the shared tree. However, it does mean that some conflicts will cause changes to revert on one side, which is a form of data loss.

## Deletions

Conflicts where an item is deleted on one or both sides are handled specially:

* If a non-folder item is changed on one side and deleted on the other, we ignore the deletion, and _revive_ the item.
* If a non-root folder is changed on one side and deleted on the other, we keep the folder deleted, and recursively move any new descendants that don't exist on the other side to the closest surviving parent folder.
* If a root folder is deleted on one side, we ignore the deletion and revive the root. This should never happen except in cases of corruption on the server.

If an item is deleted on both sides, there's no conflict, so we keep the deletion.

## Non-syncable items

A non-syncable item is:

* Any item that's not a descendant of a _user content root_ (menu, mobile, toolbar, or unfiled) on either side.
* A remote livemarks.
* A remote orphaned query.

If an item isn't syncable on either side—for example, a legacy organizer left pane query might be non-syncable locally, but orphaned and syncable remotely—it's deleted. Any syncable descendants of a non-syncable folder are relocated to the closest surviving parent folder.

## Deduping

If a remote item with the same GUID doesn't exist locally, the merger first tries to find an item with similar contents. This is called deduping. An item is a candidate for deduping if:

* It's not a root.
* It hasn't synced before. As a consequence, items that are already on the server will never dedupe to one another, even if they match.

## Invalid items

If an item on either side has an invalid GUID, the merger asks the `Driver` to generate a new one.

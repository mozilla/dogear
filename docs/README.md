# What is Dogear?

Dogear is a library that implements bookmark tree merging for [Firefox Sync](https://mozilla.github.io/application-services/docs/sync/welcome.html). It takes two trees—a valid, consistent local tree, and a possibly inconsistent remote tree—and produces a complete merged tree, with all conflicts and inconsistencies resolved.

Dogear implements the merge algorithm only; it doesn't handle syncing, storage, or application on its own. It's up to your crate to:

* Persist local and remote bookmarks in a database.
* Build trees from those bookmarks.
* Update the local and remote trees to match the merged tree, and...
* Upload records for changed bookmarks.

## Bookmark syncing

Bookmarks are [one of the more complicated data types](https://blog.nightly.mozilla.org/2018/05/14/deep-dive-new-bookmark-sync-in-nightly/) to sync. Locally, they form a hierarchy, where each bookmark lives in exactly one folder, and has a unique position within that folder.

On the server, the hierarchy is flattened into a collection of unordered, encrypted records. Folders keep pointers to their children, and children back to their parents. This means that some changes, like moving a bookmark or deleting a folder, need to upload multiple records in lockstep.

## Conflict resolution

Clients must also handle merge conflicts. Most are easy to resolve, like adding a bookmark to a folder on one side, or even adding bookmarks to the same folder on different devices. Ditto for deletions and moves.

Conflicts where a bookmark is deleted on one side and changed on the other, or where a folder is deleted on one side and has new children on the other, are harder. When resolving conflicts, it's important to flag all affected records for upload, so that the remote tree remains consistent.

Dogear manages this complexity, so that clients don't have to implement their own merging logic.

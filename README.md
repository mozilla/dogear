# Dogear

**Dogear** is a library for merging bookmark trees. The merge algorithm is used in [Firefox Desktop](https://searchfox.org/mozilla-central/rev/e9d2dce0820fa2616174396459498bcb96ecf812/toolkit/components/places/SyncedBookmarksMirror.jsm) to merge synced bookmarks, and is loosely based on the tree merger in [Firefox for iOS](https://github.com/mozilla-mobile/firefox-ios/blob/8b7b21cf1dcdbb8353a60749db9054696a1f4a5d/Sync/Synchronizers/Bookmarks/ThreeWayTreeMerger.swift). Dogear can also be used to dedupe and merge structurally similar trees; for example, when importing bookmarks.

Currently, Dogear only implements merging, and doesn't handle storage or syncing.

## Requirements

* Rust 1.31.0 or higher

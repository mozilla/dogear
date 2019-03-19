# Integrating Dogear

The cornerstone of Dogear is the `Store` trait. A `Store` implements methods for:

* Building local and remote trees.
* Fetching content info for matching bookmarks with similar contents.
* Applying the merged tree.

Exactly how this is done is up to your crate!

For example, Firefox Desktop stores local bookmarks in an [SQLite](https://sqlite.org/index.html) database called [Places](https://developer.mozilla.org/en-US/docs/Mozilla/Tech/Places/Database), and remote bookmarks in an attached ["mirror"](https://searchfox.org/mozilla-central/rev/7abb9117c8500ed20833746c9f8e800fce3a4688/toolkit/components/places/SyncedBookmarksMirror.jsm) database. During application, Desktop inserts the merged tree into a temporary, in-memory table, then uses triggers to update Places and stage outgoing items for upload.

The Rust Places library is similar to Desktop, but stores local and remote bookmarks in the same database.

However, _nothing in Dogear is SQLite-specific_. You can use a key-value store like [LMDB](https://docs.rs/rkv/0.9.4/rkv/), or even a JSON file. Also, while Dogear was developed specifically for Firefox Sync clients, you can use it to merge any two bookmark trees.

The second trait that you'll want to implement is `Driver`. The driver lets your crate customize merging behavior, including:

* Fixing up invalid item GUIDs.
* Logging.

Dogear includes a default driver that rejects invalid GUIDs, and calls the `log` crate's global logger. In Firefox Desktop, the merge driver posts log messages to the main thread, where they're sent to Sync's log manager. In Rust Places, the logger implementation sends logs to platform-specific logging backends on Android and iOS.

And that's it! Once you've implemented these two traits, you can use `Store::merge_with_driver` to run the merge and collect telemetry.

In the next section, we'll take a closer look at how to implement a `Store`.

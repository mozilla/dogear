# Content matching

`Store::fetch_new_local_contents` and `Store::fetch_new_remote_contents` provide information that the merger uses to **dedupe** new local items to incoming remote items with different GUIDs and similar contents. They return `HashMap`s that map a candidate item's GUID to its content info.

Two items are a match if they have congruent parents and matching properties:

* Bookmarks and queries match if they have the same title and URL.
* Folders match if they have the same title.
* Separators match if they have the same position in their respective parents.

Here are three suggestions for implementing `fetch_new_local_contents` and `fetch_new_remote_contents`:

* Neither should return roots.
* `fetch_new_local_contents` should only return local items that haven't been uploaded before. In Firefox Desktop and Rust Places, these are all items with a `NEW` or `UNKNOWN` sync status.
* `fetch_new_remote_contents` should only return remote items that have changed since the last sync, and don't exist locally. In Desktop and Rust Places, these are items with `needsMerge` set.

The merger still does the right thing if you don't follow these suggestions, but, depending on your storage backend, it may be more efficient if you do.

For example, you can return content info for all items in your store, if you want! This makes sense if all the content info is in memory already, or where filtering contents is more costly. On the other hand, if you're using a store like SQLite, it's more efficient to filter out contents that you know won't match in the query.

You can disable deduping entirely by returning empty `HashMap`s from these methods.

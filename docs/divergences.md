# Divergences

In the last section, the tree is totally consistent. Let's look at a case where we're not so lucky:

```json
{ "id": "menu", "type": "folder", "parentid": "places", "children": ["bookmarkAAAA"], "modified": 5 }
{ "id": "toolbar", "type": "folder", "parentid": "places", "children": ["bookmarkBBBB", "bookmarkAAAA"], "modified": 10 }
{ "id": "unfiled", "type": "folder", "parentid": "places", "children": ["bookmarkEEEE"], "modified": 5 }
{ "id": "bookmarkAAAA", "type": "bookmark", "parentid": "folderCCCCCC", "modified": 5 }
{ "id": "bookmarkDDDD", "type": "bookmark", "parentid": "menu", "modified": 5 }
{ "id": "bookmarkEEEE", "type": "bookmark", "parentid": "unfiled", "modified": 10 }
```

What's going on here?

* Both the menu and toolbar claim A as a child, but A says its `parentid` is C, which doesn't exist.
* The toolbar references B in its `children`, but B is nowhere to be found. B is a missing child.
* D says its `parentid` is the menu—which exists—but the menu doesn't mention D in its children.
* E is the only bookmark where its `parentid` matches its parent's `children`.

Yikes!

Remember that, while we can enforce hierarchical invariants for the local tree, we can't guarantee anything about the remote tree. This is because the Firefox Sync storage server can't see the contents of bookmarks, and must rely on clients alone to upload consistent data.

Unfortunately, bugs and missing features in older clients caused them to miss changes, or not upload records at all. This leads to the _structure divergences_ that we see here, like orphans, missing children, and parent-child disagreements. Newer Desktops shouldn't upload inconsistencies, but other platforms can, and many long-time Sync users have existing inconsistencies that confuse new clients when they sync for the first time.

Let's add this tree to Dogear:

```rust
# extern crate dogear;
use dogear::{Guid, IntoTree, Item, Kind, Tree, MENU_GUID, ROOT_GUID, TOOLBAR_GUID, UNFILED_GUID};
# use dogear::Result;
# fn main() -> Result<()> {
let now_millis = 11;

let mut builder = Tree::with_root(Item::root());

let mut menu = Item::new(MENU_GUID.clone(), Kind::Folder);
menu.age = now_millis - 5;
menu.needs_merge = true;
builder
    .item(menu)?
    .by_structure(&ROOT_GUID)?;

let mut toolbar = Item::new(TOOLBAR_GUID.clone(), Kind::Folder);
toolbar.age = 0;
toolbar.needs_merge = true;
builder
    .item(toolbar)?
    .by_structure(&ROOT_GUID)?;

let mut unfiled = Item::new(UNFILED_GUID.clone(), Kind::Folder);
unfiled.age = now_millis - 5;
unfiled.needs_merge = true;
builder
    .item(unfiled)?
    .by_structure(&ROOT_GUID)?;

let mut a = Item::new("bookmarkAAAA".into(), Kind::Bookmark);
a.age = now_millis - 5;
builder.item(a)?;

let mut d = Item::new("bookmarkDDDD".into(), Kind::Bookmark);
d.age = now_millis - 5;
builder.item(d)?;

let mut e = Item::new("bookmarkEEEE".into(), Kind::Bookmark);
e.age = 0;
builder.item(e)?;

// A is mentioned in both the menu's and toolbar's `children`, and its
// `parentid` is C.
builder.parent_for(&"bookmarkAAAA".into())
    .by_children(&MENU_GUID)?
    .parent_for(&"bookmarkAAAA".into())
    .by_children(&TOOLBAR_GUID)?
    .parent_for(&"bookmarkAAAA".into())
    .by_parent_guid("folderCCCCCC".into())?;

// B is mentioned in the toolbar's `children`.
builder.parent_for(&"bookmarkBBBB".into())
    .by_children(&TOOLBAR_GUID)?;

// D's `parentid` is the menu, even though it's not mentioned in the menu's
// `children`.
builder.parent_for(&"bookmarkDDDD".into())
    .by_parent_guid(MENU_GUID.clone())?;

// E's `parentid` is unfiled, and unfiled's `children` mention E.
builder.parent_for(&"bookmarkEEEE".into())
    .by_structure(&UNFILED_GUID)?;

let tree = builder.into_tree()?;
println!("{}", tree);
# Ok(())
# }
```

When we print this tree, we see:

```txt
📂 root________ (Folder; Age = 0ms)
| 📂 menu________ (Folder; Age = 6ms; Unmerged)
| | ❗️🔖 bookmarkDDDD (Bookmark; Age = 6ms)
| 📂 toolbar_____ (Folder; Age = 0ms; Unmerged)
| | ❗️🔖 bookmarkAAAA (Bookmark; Age = 6ms)
| 📂 unfiled_____ (Folder; Age = 6ms; Unmerged)
| | 🔖 bookmarkEEEE (Bookmark; Age = 0ms)
```

When Dogear built this tree, it saw inconsistencies, and decided where to keep each item based on its age. It also marked the tree structure as diverged, indicated with a ❗️, so that the merger can flag it for reupload.

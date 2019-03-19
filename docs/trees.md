# Fetching local and remote trees

First, we need to teach our `Store` to inflate trees from the storage backend. As you might expect, `fetch_local_tree` builds the local tree, and `fetch_remote_tree` builds the remote tree. The trees should be complete, so don't leave out orphans, missing children, or bookmarks with invalid GUIDs or URLs. That way, Dogear has a full picture of the state of the world.

Let's assume we've stored the following records. The current time is T = 11, A was downloaded during the last sync (at T = 6), and the menu and B during this sync:

```json
{ "id": "menu", "type": "folder", "parentid": "places", "children": ["bookmarkAAAA", "bookmarkBBBB"], "modified": 10 }
{ "id": "bookmarkAAAA", "type": "bookmark", "parentid": "menu", "modified": 5 }
{ "id": "bookmarkBBBB", "type": "bookmark", "parentid": "menu", "modified": 10 }
```

We can build a tree from those records like this, starting with the root:

```rust
# extern crate dogear;
use dogear::{Item, Tree};
let mut builder = Tree::with_root(Item::root());
```

For cases where we know the structure is valid, and the tree already contains the parent, we can use `by_structure` to indicate that the parent's `children` and child's `parentid` match. This is how we build the local tree on Desktop. Notice that we also set the `needs_merge` flag, to indicate that the menu has changes that we should merge:

```rust
# extern crate dogear;
# use dogear::{Result, Tree};
use dogear::{Guid, Item, Kind, MENU_GUID, ROOT_GUID};

# fn main() -> Result<()> {
let now_millis = 11;

# let mut builder = Tree::with_root(Item::root());
let mut menu = Item::new(MENU_GUID.clone(), Kind::Folder);
menu.age = now_millis - 10;
menu.needs_merge = true;

builder
    .item(menu)?
    .by_structure(&ROOT_GUID)?;
# Ok(())
# }
```

For cases where the `parentid` and `children` might disagree, we can set parents from `parentid` and `children` separately, using `by_parent_guid` and `by_children`. This is equivalent to `by_structure`, just slightly less efficient:

```rust
# extern crate dogear;
# use dogear::{Item, Kind, Tree, Result, MENU_GUID, ROOT_GUID};
# fn main() -> Result<()> {
# let now_millis = 11;
# let mut builder = Tree::with_root(Item::root());
# let mut menu = Item::new(MENU_GUID.clone(), Kind::Folder);
# builder.item(menu)?.by_structure(&ROOT_GUID)?;
let mut a = Item::new("bookmarkAAAA".into(), Kind::Bookmark);
a.age = now_millis - 5;

builder
    .item(a)?
    .by_parent_guid(MENU_GUID.clone())?;
builder.parent_for(&"bookmarkAAAA".into())
	.by_children(&MENU_GUID)?;
# Ok(())
# }
```

We can also insert an item without its parents, and set parents by `parentid` and `children` later, if they exist. This is also equivalent to the above:

```rust
# extern crate dogear;
# use dogear::{Item, Kind, Tree, Result, MENU_GUID, ROOT_GUID};
# fn main() -> Result<()> {
# let now_millis = 11;
# let mut builder = Tree::with_root(Item::root());
# let mut menu = Item::new(MENU_GUID.clone(), Kind::Folder);
# builder.item(menu)?.by_structure(&ROOT_GUID)?;
let mut b = Item::new("bookmarkBBBB".into(), Kind::Bookmark);
b.age = now_millis - 10;
b.needs_merge = true;

builder.item(b)?;
builder.parent_for(&"bookmarkBBBB".into())
	.by_parent_guid(MENU_GUID.clone())?;
builder.parent_for(&"bookmarkBBBB".into())
	.by_children(&MENU_GUID)?;
# Ok(())
# }
```

Finally, let's build and print out our tree!

```rust
# extern crate dogear;
# use dogear::{Item, Tree, Result};
use dogear::IntoTree;
# fn main() -> Result<()> {
# let mut builder = Tree::with_root(Item::root());
let tree = builder.into_tree()?;
println!("{}", tree);
# Ok(())
# }
```

And we see:

```txt
📂 root________ (Folder; Age = 0ms)
| 📂 menu________ (Folder; Age = 1ms; Unmerged)
| | 🔖 bookmarkAAAA (Bookmark; Age = 6ms)
| | 🔖 bookmarkBBBB (Bookmark; Age = 1ms; Unmerged)
```

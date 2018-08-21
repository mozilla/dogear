// Copyright 2018 Mozilla

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

use std::{fmt, str, ops};

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Guid(Repr);

/// The internal representation of a GUID. Valid GUIDs are 12 bytes, and contain
/// only Base64url characters; we can store them on the stack without a heap
/// allocation. However, both local and remote items might have invalid GUIDs,
/// in which case we fall back to a heap-allocated string.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum Repr {
    Fast([u8; 12]),
    Slow(String),
}

/// The Places root GUID, used to root all items in a bookmark tree.
pub const ROOT_GUID: Guid = Guid(Repr::Fast(*b"root________"));

/// The syncable Places roots. All synced items should descend from these
/// roots.
pub const USER_CONTENT_ROOTS: [Guid; 4] = [
    Guid(Repr::Fast(*b"toolbar_____")),
    Guid(Repr::Fast(*b"menu________")),
    Guid(Repr::Fast(*b"unfiled_____")),
    Guid(Repr::Fast(*b"mobile______")),
];

const VALID_GUID_BYTES: [u8; 128] =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
     0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0,
     0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0,
     0, 0, 0, 0];

impl Guid {
    #[inline]
    pub fn new(s: &str) -> Guid {
        let repr = if Guid::is_valid(s) {
            assert!(s.is_char_boundary(12));
            let mut bytes = [0u8; 12];
            bytes.copy_from_slice(s.as_bytes());
            Repr::Fast(bytes)
        } else {
            Repr::Slow(s.into())
        };
        Guid(repr)
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        match self.0 {
            Repr::Fast(ref bytes) => bytes,
            Repr::Slow(ref s) => s.as_ref(),
        }
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        // We actually could use from_utf8_unchecked here, and depending on how
        // often we end up doing this, it's arguable that we should. We know
        // already this is valid utf8, since we know that we only ever create
        // these while respecting is_valid (and moreover, we assert that
        // `s.is_char_boundary(12)` above).
        match self.0 {
            Repr::Fast(ref bytes) => str::from_utf8(bytes).unwrap(),
            Repr::Slow(ref s) => s,
        }
    }

    /// Equivalent to `PlacesUtils.isValidGuid`.
    #[inline]
    pub fn is_valid(s: &str) -> bool {
        s.len() == 12 && s.as_bytes().iter().all(
            |&byte| VALID_GUID_BYTES[(byte & 0x7f) as usize] == 1
        )
    }
}

impl<'a> From<&'a str> for Guid {
    #[inline]
    fn from(s: &'a str) -> Guid {
        Guid::new(s)
    }
}

impl AsRef<str> for Guid {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for Guid {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl ops::Deref for Guid {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

// Allow direct comparison with str
impl PartialEq<str> for Guid {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        PartialEq::eq(self.as_str(), other)
    }
}

// The default Debug impl is pretty unhelpful here.
impl fmt::Debug for Guid {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Guid({:?})", self.as_str())
    }
}

impl fmt::Display for Guid {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

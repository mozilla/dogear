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

/// The "Other Bookmarks" GUID, used to hold items without a parent.
pub const UNFILED_GUID: Guid = Guid(Repr::Fast(*b"unfiled_____"));

/// The syncable Places roots. All synced items should descend from these
/// roots.
pub const USER_CONTENT_ROOTS: [Guid; 4] = [
    Guid(Repr::Fast(*b"toolbar_____")),
    Guid(Repr::Fast(*b"menu________")),
    UNFILED_GUID,
    Guid(Repr::Fast(*b"mobile______")),
];

const VALID_GUID_BYTES: [u8; 255] =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
     0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0,
     0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0];

impl Guid {
    pub fn from_utf8(b: &[u8]) -> Option<Guid> {
        let repr = if Guid::is_valid(b) {
            let mut bytes = [0u8; 12];
            bytes.copy_from_slice(b);
            Repr::Fast(bytes)
        } else {
            match str::from_utf8(b) {
                Ok(s) => Repr::Slow(s.into()),
                Err(_) => return None
            }
        };
        Some(Guid(repr))
    }

    pub fn from_utf16(b: &[u16]) -> Option<Guid> {
        let repr = if Guid::is_valid(b) {
            let mut bytes = [0u8; 12];
            for (index, byte) in b.iter().enumerate() {
                match byte.into_byte() {
                    Some(byte) => bytes[index] = byte,
                    None => return None
                };
            }
            Repr::Fast(bytes)
        } else {
            match String::from_utf16(b) {
                Ok(s) => Repr::Slow(s),
                Err(_) => return None
            }
        };
        Some(Guid(repr))
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

    pub fn valid(&self) -> bool {
        match self.0 {
            Repr::Fast(_) => true,
            Repr::Slow(_) => false,
        }
    }

    /// Equivalent to `PlacesUtils.isValidGuid`.
    #[inline]
    fn is_valid<T: Copy + IntoByte>(bytes: &[T]) -> bool {
        bytes.len() == 12 && bytes.iter().all(|b|
            b.into_byte().map(|byte| VALID_GUID_BYTES[byte as usize] == 1).unwrap_or(false)
        )
    }
}

impl<'a> From<&'a str> for Guid {
    #[inline]
    fn from(s: &'a str) -> Guid {
        let repr = if Guid::is_valid(s.as_bytes()) {
            assert!(s.is_char_boundary(12));
            let mut bytes = [0u8; 12];
            bytes.copy_from_slice(s.as_bytes());
            Repr::Fast(bytes)
        } else {
            Repr::Slow(s.into())
        };
        Guid(repr)
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

/// `impl IntoByte for T` is almost equivalent to `impl TryFrom<T> for u8`, but
/// `TryFrom` is Nightly-only.
trait IntoByte {
    fn into_byte(self) -> Option<u8>;
}

impl IntoByte for u8 {
    #[inline]
    fn into_byte(self) -> Option<u8> {
        Some(self)
    }
}

impl IntoByte for u16 {
    #[inline]
    fn into_byte(self) -> Option<u8> {
        if self > u16::from(u8::max_value()) {
            None
        } else {
            Some(self as u8)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_valid() {
        let valid_guids = &["bookmarkAAAA",
                            "menu________",
                            "__folderBB__",
                            "queryAAAAAAA"];
        for guid in valid_guids {
            assert!(Guid::is_valid(guid.as_bytes()),
                    "{:?} should validate",
                    guid);
        }

        let invalid_guids = &["bookmarkAAA", "folder!", "b@dgu1d!"];
        for guid in invalid_guids {
            assert!(!Guid::is_valid(guid.as_bytes()),
                    "{:?} should not validate",
                    guid);
        }

        let invalid_guid_bytes: &[[u8; 12]] =
            &[[113, 117, 101, 114, 121, 65, 225, 193, 65, 65, 65, 65]];
        for bytes in invalid_guid_bytes {
            assert!(!Guid::is_valid(bytes), "{:?} should not validate", bytes);
        }
    }
}

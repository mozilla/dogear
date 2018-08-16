use std::{fmt, str, ops};

// TODO: We could store a 13th b'\0' byte for a C-compatible null terminator. Is
// this worth doing?
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Guid([u8; 12]);

// These are here so that we can create these as const/static (without needing lazy_static)
pub(crate) const ROOT_GUID: Guid = Guid(*b"root________");

pub(crate) const USER_CONTENT_ROOTS: [Guid; 4] = [
    Guid(*b"toolbar_____"),
    Guid(*b"menu________"),
    Guid(*b"unfiled_____"),
    Guid(*b"mobile______"),
];

impl Guid {
    #[inline]
    pub fn try_new(s: &str) -> Option<Guid> {
        if !Guid::is_valid(s) {
            None
        } else {
            assert!(s.is_char_boundary(12));
            let mut guid = Guid([0u8; 12]);
            guid.0.copy_from_slice(s.as_bytes());
            Some(guid)
        }
    }


    #[inline]
    pub fn new(s: &str) -> Guid {
        match Guid::try_new(s) {
            Some(g) => g,
            // We don't get to format the string passed to e.g. `expect`.
            None => panic!("Invalid guid: {:?}", s)
        }
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        // We actually could use from_utf8_unchecked here, and depending on how
        // often we end up doing this, it's arguable that we should. We know
        // already this is valid utf8, since we know that we only ever create
        // these while respecting is_valid (and moreover, we assert that
        // `s.is_char_boundary(12)` above).
        str::from_utf8(self.as_bytes()).unwrap()
    }

    /// Equivalent to `PlacesUtils.isValidGuid`.
    #[inline]
    pub fn is_valid(s: &str) -> bool {
        s.len() == 12 && s.as_bytes().iter().all(|&byte|
            // TODO: we should use a 256 entry lookup table.
            (b'0' <= byte && byte <= b'9') ||
            (b'a' <= byte && byte <= b'z') ||
            (b'A' <= byte && byte <= b'Z') ||
            b'-' == byte || b'_' == byte
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

    #[inline]
    fn ne(&self, other: &str) -> bool {
        PartialEq::ne(self.as_str(), other)
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


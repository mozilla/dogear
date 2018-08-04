/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{fmt, result};

use failure::{Backtrace, Context, Fail};

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug)]
pub struct Error(Context<ErrorKind>);

impl Fail for Error {
    #[inline]
    fn cause(&self) -> Option<&Fail> {
        self.0.cause()
    }

    #[inline]
    fn backtrace(&self) -> Option<&Backtrace> {
        self.0.backtrace()
    }
}

impl fmt::Display for Error {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl Error {
    #[inline]
    pub fn kind(&self) -> &ErrorKind {
        &*self.0.get_context()
    }
}

impl From<ErrorKind> for Error {
    #[inline]
    fn from(kind: ErrorKind) -> Error {
        Error(Context::new(kind))
    }
}

impl From<Context<ErrorKind>> for Error {
    #[inline]
    fn from(inner: Context<ErrorKind>) -> Error {
        Error(inner)
    }
}

#[derive(Debug, Fail)]
pub enum ErrorKind {
    #[fail(display = "{}", _0)]
    ConsistencyError(&'static str),
}

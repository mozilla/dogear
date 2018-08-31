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

use std::{error, fmt, result};

use guid::Guid;

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug)]
pub struct Error(ErrorKind);

impl Error {
    pub fn kind(&self) -> &ErrorKind {
        &self.0
    }
}

impl error::Error for Error {}

impl From<ErrorKind> for Error {
    fn from(kind: ErrorKind) -> Error {
        Error(kind)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Debug)]
pub enum ErrorKind {
    ConsistencyError(&'static str),
    DuplicateItemError(Guid),
    InvalidParentError(Guid, Guid),
    MissingParentError(Guid, Guid),
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::ConsistencyError(err) => write!(f, "{}", err),
            ErrorKind::DuplicateItemError(guid) => {
                write!(f, "Item {} already exists in tree", guid)
            },
            ErrorKind::InvalidParentError(child_guid, parent_guid) => {
                write!(f, "Can't insert item {} into non-folder {}",
                       child_guid, parent_guid)
            },
            ErrorKind::MissingParentError(child_guid, parent_guid) => {
                write!(f, "Can't insert item {} into nonexistent parent {}",
                       child_guid, parent_guid)
            },
        }
    }
}

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

use std::fmt::Arguments;

use crate::error::{ErrorKind, Result};
use crate::guid::Guid;

/// A merge driver provides methods to customize merging behavior.
pub trait Driver {
    /// Generates a new GUID for the given invalid GUID. This is used to fix up
    /// items with GUIDs that Places can't store (bug 1380606, bug 1313026).
    ///
    /// The default implementation returns an error, forbidding invalid GUIDs.
    ///
    /// Implementations of `Driver` can either use the `rand` and `base64`
    /// crates to generate a new, random GUID (9 bytes, Base64url-encoded
    /// without padding), or use an existing method like Desktop's
    /// `nsINavHistoryService::MakeGuid`. Dogear doesn't generate new GUIDs
    /// automatically to avoid depending on those crates.
    ///
    /// Implementations can also return `Ok(invalid_guid.clone())` to pass
    /// through all invalid GUIDs, as the tests do.
    fn generate_new_guid(&self, invalid_guid: &Guid) -> Result<Guid> {
        Err(ErrorKind::InvalidGuid(invalid_guid.clone()).into())
    }

    /// Returns the maximum level for log messages.
    fn log_level(&self) -> LogLevel {
        LogLevel::Silent
    }

    /// Logs a message at the given log level.
    fn log(&self, _level: LogLevel, _args: Arguments) {}
}

/// A default implementation of the merge driver.
pub struct DefaultDriver;

impl Driver for DefaultDriver {}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
pub enum LogLevel {
    Silent,
    Error,
    Trace,
    All,
}

#[macro_export]
macro_rules! trace {
    ($driver:expr, $($args:tt)+) => {
        if $driver.log_level() >= $crate::driver::LogLevel::Trace {
            $driver.log($crate::driver::LogLevel::Trace, format_args!($($args)+))
        }
    };
}

#[macro_export]
macro_rules! error {
    ($driver:expr, $($args:tt)+) => {
        if $driver.log_level() >= $crate::driver::LogLevel::Error {
            $driver.log($crate::driver::LogLevel::Error, format_args!($($args)+))
        }
    };
}

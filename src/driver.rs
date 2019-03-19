// Copyright 2018-2019 Mozilla

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

use log::{LevelFilter, Log};

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

    /// Returns the maximum log level for merge messages. The default
    /// implementation returns the `log` crate's global maximum level.
    fn max_log_level(&self) -> LevelFilter {
        log::max_level()
    }

    /// Returns a logger for merge messages.
    ///
    /// The default implementation returns the `log` crate's global logger.
    ///
    /// Implementations can override this method to return a custom logger,
    /// where using the global logger won't work. For example, Firefox Desktop
    /// has an existing Sync logging setup outside of the `log` crate.
    fn logger(&self) -> &Log {
        log::logger()
    }
}

/// A default implementation of the merge driver.
pub struct DefaultDriver;

impl Driver for DefaultDriver {}

#[macro_export]
macro_rules! error {
    ($driver:expr, $($args:tt)+) => (log!(Error, $driver, $($args)+));
}

macro_rules! warn {
    ($driver:expr, $($args:tt)+) => (log!(Warn, $driver, $($args)+));
}

#[macro_export]
macro_rules! debug {
    ($driver:expr, $($args:tt)+) => (log!(Debug, $driver, $($args)+));
}

#[macro_export]
macro_rules! trace {
    ($driver:expr, $($args:tt)+) => (log!(Trace, $driver, $($args)+));
}

#[macro_export]
macro_rules! log {
    ($level:ident, $driver:expr, $($args:tt)+) => {
        if log::Level::$level <= $driver.max_log_level() {
            let meta = log::Metadata::builder()
                .level(log::Level::$level)
                .target(module_path!())
                .build();
            if $driver.logger().enabled(&meta) {
                $driver.logger().log(
                    &log::Record::builder()
                        .args(format_args!($($args)+))
                        .metadata(meta)
                        .module_path(Some(module_path!()))
                        .file(Some(file!()))
                        .line(Some(line!()))
                        .build(),
                );
            }
        }
    };
}

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

use std::{collections::HashMap, fmt::Arguments, time::{Duration, Instant}};

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

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum LogLevel {
    Silent,
    Error,
    Warn,
    Debug,
    Trace,
    All,
}

/// Records timings and counters for telemetry.
#[derive(Debug, Default)]
pub struct Stats {
    timings: HashMap<Timing, Duration>,
    counts: HashMap<Counter, i64>,
}

impl Stats {
    #[inline]
    pub fn time(&mut self, key: Timing) -> TimingEntry {
        TimingEntry(self, key)
    }

    #[inline]
    pub fn count(&mut self, key: Counter) -> CounterEntry {
        CounterEntry(self, key)
    }
}

pub struct TimingEntry<'s>(&'s mut Stats, Timing);

impl<'s> TimingEntry<'s> {
    pub fn record<T, F: FnOnce() -> T>(self, func: F) -> T {
        let now = Instant::now();
        let result = func();
        self.0.timings.insert(self.1, now.elapsed());
        result
    }

    #[inline]
    pub fn as_millis(&self) -> Option<f64> {
        self.0.timings.get(&self.1)
            .map(|d| d.as_secs() as f64 + f64::from(d.subsec_micros()) / 1000.0)
    }
}

pub struct CounterEntry<'s>(&'s mut Stats, Counter);

impl<'s> CounterEntry<'s> {
    #[inline]
    pub fn set(self, value: i64) -> &'s mut Stats {
        self.0.counts.insert(self.1, value);
        self.0
    }

    #[inline]
    pub fn as_i64(&self) -> Option<i64> {
        self.0.counts.get(&self.1).cloned()
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Timing {
    FetchLocalTree,
    FetchNewLocalContents,
    FetchRemoteTree,
    FetchNewRemoteContents,
    Merge,
    Apply,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Counter {
    MergedNodes,
    MergedDeletions,
    RemoteRevives,
    LocalDeletes,
    LocalRevives,
    RemoteDeletes,
    Dupes,
}

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
        if $driver.log_level() >= $crate::driver::LogLevel::$level {
            $driver.log($crate::driver::LogLevel::$level, format_args!($($args)+));
        }
    };
}

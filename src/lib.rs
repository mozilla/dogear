/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

extern crate failure;

#[macro_use]
extern crate failure_derive;

#[macro_use]
extern crate itertools;

#[macro_use]
extern crate log;

mod error;
mod merge;
mod tree;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}

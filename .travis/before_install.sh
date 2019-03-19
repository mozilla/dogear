#!/bin/bash

set -e

if ! [ -f $HOME/.src/kcov-$KCOV_VERSION.tar.gz ]; then
  wget -O $HOME/.src/kcov-$KCOV_VERSION.tar.gz https://github.com/SimonKagstrom/kcov/archive/v$KCOV_VERSION.tar.gz
fi

if ! [ -f $HOME/.src/mdbook-$MDBOOK_VERSION ]; then
  wget -O $HOME/.src/mdbook-$MDBOOK_VERSION.tar.gz https://github.com/rust-lang-nursery/mdBook/releases/download/v$MDBOOK_VERSION/mdbook-v$MDBOOK_VERSION-x86_64-unknown-linux-gnu.tar.gz
fi

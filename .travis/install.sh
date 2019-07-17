#!/bin/bash

set -e

if [[ "$TRAVIS_RUST_VERSION" == stable ]]; then
  cargo install cargo-tarpaulin -f
fi

mkdir -p $HOME/.local/bin
pushd $HOME/.local/bin
tar xzf $HOME/.src/mdbook-$MDBOOK_VERSION.tar.gz
popd

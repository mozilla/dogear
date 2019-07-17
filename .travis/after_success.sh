#!/bin/bash

set -e

if [[ "$TRAVIS_RUST_VERSION" == stable ]]; then
  cargo tarpaulin --out Xml
  bash <(curl -s https://codecov.io/bash)
fi

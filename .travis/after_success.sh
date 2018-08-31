#!/bin/bash

set -e

for file in target/debug/dogear-*[^\.d]; do
  mkdir -p "target/cov/$(basename $file)"
  kcov --exclude-pattern=/.cargo,/usr/lib --verify "target/cov/$(basename $file)" "$file"
done
bash <(curl -s https://codecov.io/bash)

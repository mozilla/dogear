#!/bin/bash

set -e

if ! [ -f $HOME/.src/kcov-$KCOV_VERSION.tar.gz ]; then
  wget -O $HOME/.src/kcov-$KCOV_VERSION.tar.gz https://github.com/SimonKagstrom/kcov/archive/v$KCOV_VERSION.tar.gz
fi

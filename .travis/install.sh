#!/bin/bash

set -e

mkdir $HOME/.deps
pushd $HOME/.deps

tar xzf $HOME/.src/kcov-$KCOV_VERSION.tar.gz
pushd kcov-$KCOV_VERSION
mkdir build
pushd build
chronic cmake -DCMAKE_INSTALL_PREFIX=$HOME/.local ..
chronic make
chronic make install
popd
popd

popd

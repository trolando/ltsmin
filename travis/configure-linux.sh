#!/bin/bash
set -e
#set -o xtrace

export PATH=/opt/ghc/$GHCVER/bin:/opt/happy/$HAPPYVER/bin:$PATH &&
export LTSMIN_NUM_CPUS=2
export LD_LIBRARY_PATH="$HOME/ltsmin-deps/lib:$HOME/ProB/lib:$LD_LIBRARY_PATH"

# set correct compiler
# export CC="gcc"
# export CXX="g++"
# export AR="gcc-ar"
# export RANLIB="gcc-ranlib"
# export NM="gcc-nm"

export MCRL2_LIB_DIR=""

export PKG_CONFIG_PATH="$PKG_CONFIG_PATH:$HOME/ltsmin-deps/lib/pkgconfig"

. travis/configure-generic.sh "$@"

set +e


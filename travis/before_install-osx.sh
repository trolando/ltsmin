#!/bin/bash
set -e
#set -o xtrace

ls -al "$HOME/ltsmin-deps" || true
ls -al "$HOME/ltsmin-deps/lib" || true
ls -al "$HOME/ltsmin-deps/include" || true
ls -al "$HOME/ltsmin-deps/lib/pkgconfig" || true

brewIn() { if brew ls --versions "$1"; then brew upgrade "$1"; else brew install "$1"; fi }

brew update
brewIn bison
brewIn viennacl
brewIn ant
brewIn popt
brewIn libtool
brewIn dejagnu

#ghc \
#cabal-install \

#if [ ! -f "$HOME/.cabal/bin/happy" ]; then
#    cabal update
#    cabal install happy
#fi

set +e

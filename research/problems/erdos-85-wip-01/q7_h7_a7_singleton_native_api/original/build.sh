#!/bin/sh
set -eu
cd "$(dirname "$0")"
clang++ -std=c++17 -O2 -shared -fPIC filter.cpp -o filter.dylib

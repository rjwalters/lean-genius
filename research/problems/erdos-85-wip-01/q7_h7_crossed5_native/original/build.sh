#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
case "$(uname -s)" in
 Darwin) clang++ -std=c++17 -O3 -Wall -Wextra -Werror -dynamiclib filter.cpp -o filter.dylib ;;
 *) clang++ -std=c++17 -O3 -Wall -Wextra -Werror -shared -fPIC filter.cpp -o filter.dylib ;;
esac

#! /bin/sh

set -e

git clone https://github.com/bitwuzla/bitwuzla.git
cd bitwuzla
git checkout f9f197754bfbe371634e9e2134a42debc5ea0e0a
git apply ../bitwuzla.patch
make -j

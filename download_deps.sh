#! /bin/sh

set -e

git clone https://github.com/sharkdp/dbg-macro.git
cd dbg-macro && git checkout v0.5.1 && cd ..

git clone https://github.com/muellan/clipp.git
cd clipp && git checkout v1.2.3 && cd ..

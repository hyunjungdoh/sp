#!/bin/bash
# env.bc: the environment model linked into every closed program. Every
# definition is weak, so a definition the program has of its own wins.
set -e
cd "$(dirname "$0")"
F="-emit-llvm -g -O0 -Xclang -disable-O0-optnone -Wall -Wextra -Wno-unused-parameter -Wno-pointer-bool-conversion -fno-builtin"
clang-14 -c $F -o env_core.bc env.c
clang-14 -c $F -o libc.bc libc.c
clang++-14 -c $F -std=c++17 -o cxx.bc cxx.cpp
# libstdc++'s own units, from the GCC release the system's libstdc++ is
# built from, each in the language mode libstdc++ compiles it in.
clang++-14 -c $F -std=gnu++11 -o ht.bc libstdcxx/src/c++11/hashtable_c++0x.cc
clang++-14 -c $F -std=gnu++11 -o si11.bc libstdcxx/src/c++11/string-inst.cc
clang++-14 -c $F -std=gnu++17 -o si17.bc libstdcxx/src/c++17/string-inst.cc
clang++-14 -c $F -std=gnu++11 -o hb.bc libstdcxx/hash_bytes.cc
llvm-link-14 env_core.bc libc.bc cxx.bc ht.bc si11.bc si17.bc hb.bc -o env.strong.bc
llvm-dis-14 env.strong.bc -o env.ll
sed -E -i 's/^define dso_local /define weak dso_local /;
  s/^define (i[0-9]+[ *]|void |ptr |double |float |x86_fp80 |%|\{|<)/define weak \1/;
  s/^(@[A-Za-z_][A-Za-z0-9_.]*) = dso_local (global|constant)/\1 = weak dso_local \2/' env.ll
llvm-as-14 env.ll -o env.bc
rm -f env.ll env.strong.bc

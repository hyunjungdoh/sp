#!/bin/bash
# Runs inside klee/klee:latest with the repo root mounted at /w: rebuilds
# /w/env/env.bc from libc.c and env.c and the prebuilt C++ units. Every
# definition is weak, so a definition the program has of its own wins.
set -e
cd /w/env/src
L=/tmp/llvm-180-install_O_D_A/bin
F="-emit-llvm -g -O0 -Xclang -disable-O0-optnone -Wall -Wextra -Wno-unused-parameter -Wno-pointer-bool-conversion -fno-builtin"
$L/clang -c $F -o env_core.bc env.c
$L/clang -c $F -o libc.bc libc.c
$L/llvm-link env_core.bc libc.bc cxx.bc ht.bc si11.bc si17.bc hb.bc -o /tmp/env.strong.bc
$L/llvm-dis /tmp/env.strong.bc -o /tmp/env.ll
sed -E -i 's/^define dso_local /define weak dso_local /;
  s/^define (i[0-9]+[ *]|void |ptr |double |float |x86_fp80 |%|\{|<)/define weak \1/;
  s/^(@[A-Za-z_][A-Za-z0-9_.]*) = dso_local (global|constant)/\1 = weak dso_local \2/' /tmp/env.ll
$L/llvm-as /tmp/env.ll -o /w/env/env.bc

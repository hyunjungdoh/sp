/*===-- strcmp.c ----------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===*/

#include "klee/klee.h"

// The result is a value of the characters: the first position where they
// differ or a ends decides it, selected without branching on them. The scan
// stops at a concrete NUL of either string, and forks only where both
// characters are symbolic and whether the scan goes on is undecided.
int strcmp(const char *a, const char *b) {
  const unsigned char *p = (const unsigned char *)a;
  const unsigned char *q = (const unsigned char *)b;
  int r = 0, live = 1;

  for (;; ++p, ++q) {
    unsigned char x = *p, y = *q;
    int d = (int)x - (int)y;
    int stop = live & ((d != 0) | (x == 0));
    int m = -stop;
    r = (d & m) | (r & ~m);
    live = live & (stop == 0);
    if (!klee_is_symbolic(x) && x == 0)
      break;
    if (!klee_is_symbolic(y) && y == 0)
      break;
    if (!klee_is_symbolic(live) && !live)
      break;
    if (klee_is_symbolic(x) && klee_is_symbolic(y) && !live)
      break;
  }

  return r;
}

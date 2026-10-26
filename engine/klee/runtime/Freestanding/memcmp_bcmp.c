/*===-- memcmp_bcmp.c -----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===*/

#include <stddef.h>

// The result is a value of the bytes, not a path per first difference: the
// lowest differing position wins, selected without branching on the bytes.
int memcmp(const void *s1, const void *s2, size_t n) {
  const unsigned char *a = s1;
  const unsigned char *b = s2;
  int r = 0;

  while (n) {
    n--;
    int d = (int)a[n] - (int)b[n];
    int m = -(int)(d != 0);
    r = (d & m) | (r & ~m);
  }

  return r;
}

int bcmp(const void *s1, const void *s2, size_t n) { return memcmp(s1, s2, n); }

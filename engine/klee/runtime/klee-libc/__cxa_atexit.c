/*===-- __cxa_atexit.c ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===*/

#include "klee/klee.h"

#include <stdlib.h>

/* The C++ ABI sets no limit on registrations (one per static object with a
 * destructor), so the list grows; it runs last registered first. */
struct AtExitEntry {
  void (*fn)(void*);
  void *arg;
  struct AtExitEntry *next;
};
static struct AtExitEntry *AtExit = 0;

static void RunAtExit(void) __attribute__((destructor));
static void RunAtExit(void) {
  struct AtExitEntry *e;

  for (e = AtExit; e; e = e->next)
    e->fn(e->arg);
}

int __cxa_atexit(void (*fn)(void*),
                 void *arg,
                 void *dso_handle) {
  struct AtExitEntry *e;

  klee_warning_once("FIXME: __cxa_atexit being ignored");

  e = malloc(sizeof *e);
  if (!e)
    return -1;
  e->fn = fn;
  e->arg = arg;
  e->next = AtExit;
  AtExit = e;

  return 0;
}

// This variant is part of more recent glibc versions and
// is required by the Rust standard library
int __cxa_thread_atexit_impl(void (*fn)(void*), void *arg, void *dso_handle) {
  return __cxa_atexit(fn, arg, dso_handle);
}

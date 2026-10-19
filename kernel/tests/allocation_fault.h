/* Test-only redirection, after libc has declared its own allocator. */
#ifndef CC_TEST_ALLOCATION_FAULT_H
#define CC_TEST_ALLOCATION_FAULT_H
#include <stdlib.h>
void *cc_test_calloc(size_t count, size_t size);
#undef calloc
#define calloc(count, size) cc_test_calloc((count), (size))
#endif

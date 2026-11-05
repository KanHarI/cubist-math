/* Test-only redirection, after libc has declared its own allocator: the
 * growth of the instruction store's arrays. */
#ifndef CC_TEST_ALLOCATION_FAULT_H
#define CC_TEST_ALLOCATION_FAULT_H
#include <stdlib.h>
void *cc_test_realloc(void *pointer, size_t size);
#undef realloc
#define realloc(pointer, size) cc_test_realloc((pointer), (size))
#endif

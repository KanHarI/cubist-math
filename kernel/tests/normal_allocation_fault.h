/* Redirect only the normalizer object in the allocation-failure test. */
#ifndef CC_TEST_NORMAL_ALLOCATION_FAULT_H
#define CC_TEST_NORMAL_ALLOCATION_FAULT_H
#include <stdlib.h>
void *cc_test_normal_malloc(size_t size);
void *cc_test_normal_realloc(void *pointer, size_t size);
#undef malloc
#define malloc(size) cc_test_normal_malloc(size)
#undef realloc
#define realloc(pointer, size) cc_test_normal_realloc((pointer), (size))
#endif

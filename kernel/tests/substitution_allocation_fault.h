/* Only the substitution test binary redirects this source's allocators. */
#ifndef CC_TEST_SUBSTITUTION_ALLOCATION_FAULT_H
#define CC_TEST_SUBSTITUTION_ALLOCATION_FAULT_H
#include <stdlib.h>
void *cc_test_substitution_malloc(size_t size);
void *cc_test_substitution_realloc(void *pointer, size_t size);
#undef malloc
#define malloc(size) cc_test_substitution_malloc(size)
#undef realloc
#define realloc(pointer, size) cc_test_substitution_realloc(pointer, size)
#endif

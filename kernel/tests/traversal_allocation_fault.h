#include <stddef.h>
#include <stdlib.h>
void *cc_test_traversal_malloc(size_t);
void *cc_test_traversal_realloc(void *, size_t);
void *cc_test_traversal_calloc(size_t, size_t);
#define malloc cc_test_traversal_malloc
#define realloc cc_test_traversal_realloc
#define calloc cc_test_traversal_calloc

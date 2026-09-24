#ifndef CUBICAL_INTERNAL_H
#define CUBICAL_INTERNAL_H
#include "cubical.h"

bool cc_valid_sort(cc_sort);
bool cc_clause_subset(cc_clause, cc_clause);
cc_status cc_insert(cc_formula *, cc_clause);
cc_status cc_insert_work(cc_formula *, cc_clause, size_t *);
cc_status cc_join_work(cc_formula *, const cc_formula *, const cc_formula *, size_t *);
cc_status cc_meet_work(cc_formula *, const cc_formula *, const cc_formula *, size_t *);
void cc_publish(cc_formula *output, cc_formula *candidate);

#endif

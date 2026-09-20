#ifndef CUBICAL_INTERNAL_H
#define CUBICAL_INTERNAL_H
#include "cubical.h"

bool cc_valid_sort(cc_sort);
bool cc_clause_subset(cc_clause, cc_clause);
cc_status cc_insert(cc_formula *, cc_clause);
void cc_publish(cc_formula *output, cc_formula *candidate);

#endif

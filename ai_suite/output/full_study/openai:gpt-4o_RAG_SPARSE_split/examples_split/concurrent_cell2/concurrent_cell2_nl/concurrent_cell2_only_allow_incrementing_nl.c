#include "prelude.h"

// Specification for atomic_load
/*@
predicate atomic_cell(int *c; int value);

fixpoint bool is_atomic_cell(int *c) {
    return true;
}

lemma void atomic_cell_unique(int *c);
    requires [?f]atomic_cell(c, ?v1) &*& [?g]atomic_cell(c, ?v2);
    ensures [f]atomic_cell(c, v1) &*& [g]atomic_cell(c, v2) &*& v1 == v2;

lemma void atomic_cell_limits(int *c);
    requires [?f]atomic_cell(c, ?v);
    ensures [f]atomic_cell(c, v) &*& INT_MIN <= v &*& v <= INT_MAX;

@*/

// atomic_load function specification
/*@
requires atomic_cell(c, ?value);
ensures atomic_cell(c, value) &*& result == value;
@*/
int atomic_load(int* c);

// only_allow_incrementing function
// TODO: make this function pass the verification
/*@
requires atomic_cell(c, ?value);
ensures atomic_cell(c, ?new_value) &*& value <= new_value;
@*/
void only_allow_incrementing(int* c)
{
  int x1 = atomic_load(c);
  int x2 = atomic_load(c);
  assert(x1 <= x2);
}
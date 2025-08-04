//@ requires integer(cell, ?value) &*& value >= INT_MIN &*& value < INT_MAX;
//@ ensures integer(cell, value + 1);
lemma void integer_limits(int *p);
    requires [?f]integer(p, ?v);
    ensures [f]integer(p, v) &*& object_pointer_within_limits(p, sizeof(int)) == true &*& INT_MIN <= v &*& v <= INT_MAX;
#include "stdlib.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = integer(cell, value) &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = integer(cell, value);


// TODO: make this function pass the verification
void increment(int *cell)
    //@ requires integer(cell, ?value) &*& value >= INT_MIN &*& value < INT_MAX;
    //@ ensures integer(cell, value + 1);
{
    //@ integer_limits(cell);
    (*cell)++;
}
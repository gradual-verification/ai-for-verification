#include "prelude.h"

/*atomic_load function
-param: c: pointer to the cell
-description: atomically load and return the value of the cell.

It doesn't have any implementation.

It ensures that the old trace is the prefix of current trace.
*/
//@ predicate atomic_load_pre(int *c, int value) = integer(c, value);
//@ predicate atomic_load_post(int *c, int value) = integer(c, value);

int atomic_load(int* c);
    //@ requires atomic_load_pre(c, ?value);
    //@ ensures atomic_load_post(c, value) &*& result == value;

// TODO: make this function pass the verification
/*only_allow_incrementing function
-param: c: pointer to the cell
-description: check whether only incrementing operation is done on a cell. 

It uses an assert statement to show that two loads doesn't decrement the value. 
*/
void only_allow_incrementing(int* c)
    //@ requires integer(c, ?v);
    //@ ensures integer(c, ?v2) &*& v <= v2;
{
  int x1 = atomic_load(c);
  int x2 = atomic_load(c);
  //@ assert x1 <= x2;
  assert(x1 <= x2);
}
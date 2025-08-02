#include "prelude.h"

// TODO: make this function pass the verification
/*atomic_load function
-param: c: pointer to the cell
-description: atomically load and return the value of the cell.

It doesn't have any implementation.

It ensures that the old trace is the prefix of current trace.
*/
int atomic_load(int* c);
    //@ requires [?f]integer(c, ?v);
    //@ ensures [f]integer(c, v) &*& result == v;
{
    //@ open [f]integer(c, v);
    int result = *c;
    //@ close [f]integer(c, v);
    return result;
}
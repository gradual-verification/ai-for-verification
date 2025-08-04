#include "stdlib.h"

struct Counter {
  int value;
};

/*@
// A predicate representing ownership of a Counter struct.
// It owns the 'value' field and the malloc_block for the struct.
predicate counter(struct Counter *c; int value) =
    c->value |-> value &*&
    malloc_block_Counter(c);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The dispose function frees the memory allocated for the Counter.

@param c: a pointer to a Counter

The function makes sure that the counter c is freed.
*/
void dispose(struct Counter* c)
    //@ requires counter(c, ?v);
    //@ ensures emp;
{
    //@ open counter(c, v);
    free(c);
}
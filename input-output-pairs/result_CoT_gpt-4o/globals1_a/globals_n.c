#include "stdlib.h"

/* Declare a predicate for managing the structure's memory */
predicate counter(struct counter *c, int f) = 
    c->f |-> f;

/* Declare a predicate for managing the global pointer memory */
predicate counter_global(struct counter *c) = 
  c != 0 &*& malloc_block_counter(c) &*& counter(c, ?f);

/* Declare a predicate for managing the global variable x */
predicate x_global() = 
  &x |-> ?v;

/*  
 * Given that:
 *  - We have a global integer `x`.
 *  - We have a global pointer `c` referencing a `struct counter`.
 * Precondition and postcondition for m()
 */
/*@
requires x_global() &*& counter_global(c);
ensures x_global() &*& counter(c, ?new_f) &*& new_f == old_f + 1;
@*/
void m()
//@ requires x_global() &*& counter(c, ?old_f);
//@ ensures x_global() &*& counter(c, old_f + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

/*
 * Entry point of the program.
 * Precondition and postcondition for main()
 */
/*@
requires true;
ensures true;
@*/
int main()
//@ requires true;
//@ ensures true;
{
    x = 7;
    //@ close x_global();
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    //@ close malloc_block_counter(ctr);
    ctr->f = 42;
    //@ close counter(ctr, 42);
    c = ctr;
    //@ close counter_global(c);
    
    m();
    // Obtain the updated f value
    //@ open counter_global(c);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ leak malloc_block_counter(c);
    //@ leak counter(c, _);
    free(ctr);
    return 0;
}

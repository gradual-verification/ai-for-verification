#include "stdlib.h"

// Global variable
static int x;

// Structure definition
struct counter {
    int f;
};

// Global pointer to the structure
static struct counter *c;

/*@ 
predicate counter(struct counter *ctr, int f) =
    ctr != 0 &*& ctr->f |-> f &*& malloc_block_counter(ctr);
@*/


void m()
//@ requires x |-> ?old_x &*& c |-> ?ctr &*& counter(ctr, ?old_f) &*& old_x + 1 <= INT_MAX &*& old_f + 1 <= INT_MAX;
//@ ensures x |-> old_x + 1 &*& c |-> ctr &*& counter(ctr, old_f + 1);
{
    int y = x;
    x = y + 1;
    //@ open counter(ctr, old_f);
    c->f = c->f + 1;
    //@ close counter(ctr, old_f + 1);
}


int main() //@ : main_full(globals_n)
//@ requires module(globals_n, true);
//@ ensures result == 0;
{
    //@ open_module();
    x = 7;
    
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    
    ctr->f = 42;
    c = ctr;
    
    //@ close counter(c, 42);
    m();
    //@ open counter(c, 43);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    
    
    free(ctr);
    
    return 0;
    //@ leak integer(&x, _) &*& pointer(&c, _);
}

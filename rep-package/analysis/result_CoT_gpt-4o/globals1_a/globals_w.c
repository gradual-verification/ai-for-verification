#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

//@ predicate counter(struct counter* c; int v) = c->f |-> v;

void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter(ctr, ?v) &*& malloc_block_counter(ctr) &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter(ctr, v + 1) &*& malloc_block_counter(ctr);
{
    //@ open counter(ctr, v);
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
    //@ close counter(ctr, v + 1);
}

int main() //@ : main_full(globals_w)
//@ requires module(globals_w, true);
//@ ensures true;
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    
    // @ close counter(ctr, 42);
    ctr->f = 42;
    c = ctr;
    //@ close counter(ctr, 42);  // Counter initialized according to the predicate

    m();
    
    //@ open counter(ctr, 43);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    
    //@ open counter(ctr, 43);
    free(ctr);
    return 0;
    //@ leak integer(&x, _) &*& pointer(&c, _);
}

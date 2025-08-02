#include "stdlib.h"

static int x;

struct counter {
    int f;
};

//@ predicate counter_f(struct counter* c, int v) = c->f |-> v &*& malloc_block_counter(c);

static struct counter *c;


void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v);
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}


int main() //@ : main_full(globals_main_fb)
//@ requires module(globals_main_fb, true);
//@ ensures true;
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    
    //@ close counter_f(ctr, 42);
    //@ close x |-> 7;
    //@ close c |-> ctr;
    m();
    //@ open c |-> ctr;
    //@ open counter_f(ctr, 43);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    free(ctr);
    return 0;
}
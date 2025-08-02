#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

//@ predicate counter_f(struct counter *ctr, int v) = ctr->f |-> v &*& malloc_block_counter(ctr);

void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v);
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

// TODO: make this function pass the verification
int main() //@ : main_full(globals_main_fb)
//@ requires module(globals_main_fb, true);
//@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    //@ close counter_f(ctr, 42);
    c = ctr;
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ open counter_f(ctr, 43);
    free(ctr);
    return 0;
}
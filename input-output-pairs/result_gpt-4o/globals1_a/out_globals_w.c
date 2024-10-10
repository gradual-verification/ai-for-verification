#include "stdlib.h"

static int x;

struct counter {
    int f;
};

//@ predicate counter(struct counter* c, int v) = c->f |-> v;

void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter(ctr, ?v); 
//@ ensures x |-> 8 &*& c |-> ctr &*& counter(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

int main() //@ : main_full(main)
//@ requires true;
//@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    //@ close counter(ctr, 42);
    ctr->f = 42;
    c = ctr;
    //@ close c |-> ctr;
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ open counter(ctr, _);
    free(ctr);
    return 0;
}

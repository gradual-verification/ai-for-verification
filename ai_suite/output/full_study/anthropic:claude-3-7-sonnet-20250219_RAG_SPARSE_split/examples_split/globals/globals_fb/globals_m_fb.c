#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

//@ predicate counter_f(struct counter* ctr, int v) = ctr->f |-> v;

// TODO: make this function pass the verification
void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v);
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    //@ assert y == 7;
    x = y + 1;
    //@ assert x == 8;
    
    //@ open counter_f(ctr, v);
    c->f = c->f + 1;
    //@ close counter_f(ctr, v + 1);
}
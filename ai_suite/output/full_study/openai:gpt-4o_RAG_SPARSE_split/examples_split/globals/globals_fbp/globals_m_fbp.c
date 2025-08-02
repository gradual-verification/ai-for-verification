#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

// TODO: make this function pass the verification
void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v) &*& v >= INT_MIN &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    //@ produce_limits(y);
    x = y + 1;
    //@ assert x == y + 1;
    //@ assert x == 8;
    //@ open counter_f(ctr, v);
    int cf = c->f;
    //@ produce_limits(cf);
    c->f = cf + 1;
    //@ close counter_f(ctr, cf + 1);
}

//@ predicate counter_f(struct counter *ctr, int v) = ctr->f |-> v;
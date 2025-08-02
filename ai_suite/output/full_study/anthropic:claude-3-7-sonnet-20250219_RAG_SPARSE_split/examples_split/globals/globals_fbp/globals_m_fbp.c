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
    
    //@ open counter_f(ctr, v);
    int old_f = c->f;
    //@ produce_limits(old_f);
    //@ assert old_f == v;
    
    // Check for overflow before incrementing
    if (old_f == INT_MAX) {
        abort();
    }
    
    c->f = old_f + 1;
    //@ close counter_f(ctr, v + 1);
}
#include "stdlib.h"

static int x; // Global variable

struct counter {
    int f;
};

static struct counter *c; // Global pointer to a counter

//@ predicate counter(struct counter* c, int v) = c->f |-> v;

void m()
//@ requires integer(&x, 7) &*& c |-> ?ctr &*& counter(ctr, ?v) &*& v + 1 <= INT_MAX;
//@ ensures integer(&x, 8) &*& c |-> ctr &*& counter(ctr, v + 1);
{   
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

int main() //@ : main_full(globals_m)
//@ requires module(globals_m, true);
//@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    //@ close counter(ctr, 42);
    //@ close c |-> ctr;
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ open c |-> ctr;
    //@ open counter(ctr, 43);
    free(ctr);
    return 0;
}

#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

//no counter_f defined, defined my own one
//@ predicate counter_f(struct counter* c, int v) = c->f |-> v

void m()
//@ requires x == 7 &*& counter_f(c, ?v)
//@ ensures x == 8 &*& counter_f(c, v+1)
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

int main() //@ : main_full(globals)
    //@ requires module(globals, true);
    //@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    free(ctr);
    return 0;
}
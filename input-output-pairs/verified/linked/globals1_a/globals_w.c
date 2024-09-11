#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

//no counter_f defined, defined my own one
//@ predicate counter(struct counter* c, int v) = c->f |-> v;

void m()
//@ requires x == 7 &*& *(&c) |-> ?ctr &*& counter(ctr, ?v); // have to leave pointer/extra sep arrow in here even in weak version since global variable c can't be used in counter(c, ?v) directly
//@ ensures x == 8 &*& *(&c) |-> ctr &*& counter(ctr, v+1);  // pointer(&c, ?ctr) is equivalent to saying *(&c) |-> ?ctr with a few extra contrains
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
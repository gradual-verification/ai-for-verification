#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;


void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v);
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}


// TODO: make this function pass the verification
int main() //@ : main_full(globals_fb)
//@ requires module(globals_fb, true);
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
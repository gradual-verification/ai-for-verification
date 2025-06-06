#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

//@ predicate counter(struct counter* c, int v) = c->f |-> v;

void m()
//@ requires integer(&x, 7) &*& c |-> ?ctr &*& counter(ctr, ?v) &*& v + 1 <= INT_MAX;
//@ ensures integer(&x, 8) &*& c |-> ctr &*& counter(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    //@ open counter(ctr, v);
    c->f = c->f + 1;
    //@ close counter(ctr, v + 1);
}

int main() //@ : main_full(globals_fbp)
//@ requires module(globals_fbp, true);
//@ ensures true;
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    //@ close counter(ctr, 42);
    //@ close integer(&x, 7);
    // @ close c |-> ctr;
    m();
    //@ open counter(ctr, 43);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    // @ open c |-> ctr;
    //@ open integer(&x, 8);
    // @ open counter(ctr, 43);
    free(ctr);
    //@ leak integer(&x, _) &*& pointer(&c, _);
    return 0;
}

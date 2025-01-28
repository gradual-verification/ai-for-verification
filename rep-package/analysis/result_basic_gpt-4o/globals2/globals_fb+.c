#include "stdlib.h"

// Define predicate for the counter structure
// @ predicate counter_f(struct counter *ctr, int v) = ctr->f |-> v;

static int x;
static struct counter *c;

struct counter {
    int f;
};

void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v) &*& v >= INT_MIN &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
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
    //@ close counter_f(ctr, 42);
    c = ctr;
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ open counter_f(ctr, 43);
    free(ctr);
    return 0;
    //@ leak integer(&x, _) &*& pointer(&c, _);
}

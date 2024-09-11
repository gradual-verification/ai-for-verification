#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

//@ predicate counter(struct counter* c, int v) = c->f |-> v;

// see https://github.com/verifast/verifast/commit/f8f060b2ac4dd2bb6556b334467f55fe8b3ce031
void m()
    //@ requires integer(&x, 7) &*& c |-> ?ctr &*& counter(ctr, ?v) &*& INT_MIN <= v &*& v + 1 <= INT_MAX; // added int bound assumptions due to VeriFast needing it to verify this example
    //@ ensures integer(&x, 8) &*& c |-> ctr &*& counter(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    //@ open counter(ctr, v);
    c->f = c->f + 1;
    //@ close counter(ctr, v + 1);
}

int main() //@ : main_full(globals)
    //@ requires module(globals, true);
    //@ ensures true;
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    //@ close counter(c, 42);
    m();
    //@ open counter(c, 43);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    free(ctr);
    //@ leak integer(&x, _) &*& pointer(&c, _);
    return 0;
}
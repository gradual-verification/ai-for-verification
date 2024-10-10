#include "stdlib.h"

struct counter {
    int f;
};

struct counter *c;


//@ predicate counter(struct counter *ctr, int v) = ctr->f |-> v;

void m()
//@ requires c |-> ?ctr &*& counter(ctr, ?v) &*& v >= INT_MIN &*& v + 1 <= INT_MAX;
//@ ensures c |-> ctr &*& counter(ctr, v + 1);
{
    c->f = c->f + 1;
}

int main() //@ : main_full()
//@ requires true;
//@ ensures true;
{
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    m();
    free(ctr);
    return 0;
}

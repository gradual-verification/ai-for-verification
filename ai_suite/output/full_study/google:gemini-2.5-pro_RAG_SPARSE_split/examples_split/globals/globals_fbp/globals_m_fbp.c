#include "stdlib.h"
//@ #include "prelude.h"

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
    x = y + 1;
    c->f = c->f + 1;
}
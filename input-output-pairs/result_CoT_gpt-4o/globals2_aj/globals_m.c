#include "stdlib.h"

static int x;

struct counter {
    int f;
};

// Predicate for the struct counter
// Represents ownership and encapsulates the invariants related to 'f'
predicate counter_f(struct counter *ctr, int v) =
    ctr != 0 &*& ctr->f |-> v &*& v >= INT_MIN &*& v <= INT_MAX;

static struct counter *c;

void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v) &*& v >= INT_MIN &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    // Open the counter_f predicate to access fields of 'ctr'
    //@ open counter_f(ctr, v);
    int y = x;
    x = y + 1;
    ctr->f = ctr->f + 1;
    // Close the counter_f predicate after modifying the field
    //@ close counter_f(ctr, v + 1);
}

int main() //@ : main_full(globals_m)
//@ requires module(globals_m, true);
//@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();

    // Initialize the struct counter and establish its predicate
    ctr->f = 42;
    //@ close counter_f(ctr, 42);

    c = ctr;
    m();

    // Having called m(), the predicate counter_f(ctr, 43) should hold
    int ctr_f = ctr->f;
    assert(ctr_f == 43);

    // Open the counter_f predicate to release ownership before freeing memory
    //@ open counter_f(ctr, 43);
    free(ctr);
    return 0;
}

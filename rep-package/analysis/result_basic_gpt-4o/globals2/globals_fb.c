#include "stdlib.h"

static int x;

struct counter {
    int f;
};

// Predicate to describe the state of the counter
// @ predicate counter_f(struct counter *ctr, int f) = ctr->f |-> f;

static struct counter *c;

// Function to update global variables `x` and `c->f`
void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v) &*& v >= INT_MIN &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

int main() //@ : main_full(globals_fb)
//@ requires module(globals_fb, true);
//@ ensures true;
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;

    // Establish initial predicate state
    //@ open counter_f(ctr, 42);

    m();

    // Verify the updated predicate state
    //@ assert ctr->f |-> 43; 
    //@ close counter_f(ctr, 43);

    int ctr_f = ctr->f;
    assert(ctr_f == 43);

    //@ open counter_f(ctr, 43); // Opening the predicate before deallocating memory
    free(ctr);

    return 0;
    //@ leak integer(&x, _) &*& pointer(&c, _);
}

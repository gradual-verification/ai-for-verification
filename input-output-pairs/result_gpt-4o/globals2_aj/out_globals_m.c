#include "stdlib.h"
#include "limits.h"

static int x;

struct counter {
    int f;
};

// Predicate to represent the state of a `counter` struct.
predicate counter_f(struct counter *ctr; int v) =
    ctr->f |-> v;

static struct counter *c;

// Function `m` with proper specification for Verifast.
void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v) &*& v >= INT_MIN &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

int main() //@ : main_full(globals_m)
//@ requires module(globals_m, true);
//@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    
    // Set up the initial predicate
    //@ close counter_f(ctr, 42);
    
    m();
    
    // Verify that the counter has been incremented correctly
    int ctr_f = ctr->f;
    //@ open counter_f(ctr, 43);
    
    assert(ctr_f == 43);
    
    // Proper cleanup of the counter
    //@ open counter_f(ctr, _);
    free(ctr);
    return 0;
}

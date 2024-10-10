#include "stdlib.h"

// Declare global variables
static int x;
static struct counter *c;

// Define counter struct
struct counter {
    int f;
};

// Predicate for counter object
predicate counter_f(struct counter *c, int v) =
    c != 0 &*& c->f |-> v;

void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v);
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    //@ open counter_f(ctr, v);  // Open the predicate for counter
    x = y + 1;
    c->f = c->f + 1;
    //@ close counter_f(ctr, v + 1);  // Close the predicate with the updated value
}

int main() //@ : main_full(globals_w)
//@ requires module(globals_w, true);
//@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    //@ close counter_f(ctr, 42);  // Initialize the predicate for the counter instance
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ open counter_f(ctr, 43);  // Open the predicate to access the counter field
    free(ctr);
    return 0;
}

#include "stdlib.h"

// Define a predicate to represent the state of the counter structure.
//@ predicate counter_f(struct counter *ctr, int f) = ctr->f |-> f;

static int x;

struct counter {
    int f;
};

static struct counter *c;

// Function m increments x and the field f of struct 'counter' by 1.
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v);
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
void m()
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

// Main function allocates a counter, sets initial values and asserts postconditions.
//@ requires module(globals_w, true);
//@ ensures true;
int main() //@ : main_full(globals_w)
{
    x = 7;
    
    // Allocate memory for 'counter' struct and ensure allocation succeeded.
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    
    // Initialize the counter and the global variable 'c'.
    ctr->f = 42;
    c = ctr;

    // Initialize and open predicate for structured verification.
    //@ close counter_f(ctr, 42);
    //@ close c |-> ctr;
    m();
    
    // Extract and validate the updated value of f post function call.
    //@ open counter_f(ctr, _);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    
    // Free the allocated memory for the counter structure.
    free(ctr);
    return 0;
}

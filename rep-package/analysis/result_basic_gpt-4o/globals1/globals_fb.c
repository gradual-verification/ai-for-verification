#include "stdlib.h"

// Declare global variable x
static int x;

// Define a structure named counter
struct counter {
    int f;
};

// Declare a global pointer to a counter
static struct counter *c;

// Predicate representing the state of a counter
//@ predicate counter(struct counter* c, int v) = c->f |-> v;

void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter(ctr, ?v) &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter(ctr, v + 1);
{
    // Assign current value of x to y
    int y = x;
    // Increment the value of x
    x = y + 1;
    // Increment the value of counter's field f
    //@ open counter(ctr, v);
    c->f = c->f + 1;
    //@ close counter(ctr, v + 1);
}

int main() //@ : main_full(globals_fb)
//@ requires module(globals_fb, true);
//@ ensures true;
{
    //@ open_module();
    // Assign 7 to global variable x
    x = 7;
    
    // Allocate memory for a counter instance
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();

    // Initialize counter's field value f
    ctr->f = 42;
    
    // Assign global pointer c to the newly created counter
    c = ctr;

    // Verify the counter predicate
    //@ close counter(ctr, 42);
    // @ open x |-> 7;
    // @ open c |-> ctr;
    
    // Call function m
    m();
    
    // Verify the updated counter predicate
    
    //@ assert x |-> 8 &*& c |-> ctr &*& counter(ctr, 43);
    //@ open counter(c, 43);

    // Assert to check the correctness
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    
    // Free allocated memory
    free(ctr);
    
    return 0;
    //@ leak integer(&x, _) &*& pointer(&c, _);
}

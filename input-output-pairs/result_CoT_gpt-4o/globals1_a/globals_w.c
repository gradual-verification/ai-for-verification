#include "stdlib.h"

static int x;

// Define a struct for counter
struct counter {
    int f;
};

// Pointer to the counter struct
static struct counter *c;

//@ predicate counter(struct counter* c, int v) = c->f |-> v;

void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter(ctr, ?v); 
//@ ensures x |-> 8 &*& c |-> ctr &*& counter(ctr, v + 1);
{
    // Open the counter predicate
    //@ open(counter(ctr, v));
    
    int y = x; // Read the global x
    x = y + 1; // Increment the global x
    
    // Increment the field f of the counter struct pointed by c
    c->f = c->f + 1;
    
    // Close the counter predicate
    //@ close(counter(ctr, v + 1));
}

int main() 
//@ : main_full(globals_w)
//@ requires module(globals_w, true);
//@ ensures true;
{
    // Initialize x
    x = 7;
    
    // Allocate memory for a counter struct
    struct counter *ctr = malloc(sizeof(struct counter));
    
    // Check if allocation was successful
    if (ctr == 0) abort();

    // Initialize the field f of the counter struct
    ctr->f = 42;
    
    // Set the global counter pointer
    c = ctr;
    
    // Open pointer to ctr
    //@ open(c |-> _);
    //@ close c |-> ctr;
    
    // Establish the counter predicate for the struct
    //@ close counter(ctr, 42);
    
    // Call the function m()
    m();

    // Get the field f of the counter struct to assert its value
    int ctr_f = ctr->f;
    
    // Assert to validate the expected value of f
    assert(ctr_f == 43);
    
    // Deallocate the counter struct
    free(ctr);
    
    return 0;
}

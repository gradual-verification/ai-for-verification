#include "stdlib.h"

// Global variable definition
static int x;

// Struct definition
struct counter {
    int f;
};

// Static global counter definition
static struct counter *c;

// Predicate definition to describe the structure and its content
predicate counter_f(struct counter *ctr, int v) = 
    ctr->f |-> v;  

// Function m
void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v);
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

// Main function
int main() //@ : main_full(globals_w)
//@ requires module(globals_w, true);
//@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    
    // Open predicate before calling m()
    //@ open c |-> ctr;
    //@ open counter_f(ctr, _);
    m();
    //@ close counter_f(ctr, 43);
    //@ close c |-> ctr;
    
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    
    // Leak statements for memory allocation checks
    //@ open counter_f(ctr, 43);
    //@ leak c |-> ctr;
    //@ leak malloc_block_counter(ctr);
    
    free(ctr);
    return 0;
}

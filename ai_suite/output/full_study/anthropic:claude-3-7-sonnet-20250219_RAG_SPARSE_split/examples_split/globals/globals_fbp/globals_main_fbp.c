#include "stdlib.h"

//@ #include "list.gh"

static int x;

struct counter {
    int f;
};

//@ predicate counter_f(struct counter* c, int v) = c->f |-> v;

static struct counter *c;


void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v) &*& v >= INT_MIN &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}


int main() //@ : main_full(globals_main_fbp)
//@ requires module(globals_main_fbp, true);
//@ ensures true;
{
    //@ open_module();
    
    x = 7;
    //@ close x |-> 7;
    
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    
    ctr->f = 42;
    //@ close counter_f(ctr, 42);
    
    c = ctr;
    //@ close c |-> ctr;
    
    m();
    
    int ctr_f = ctr->f;
    //@ open counter_f(ctr, _);
    
    assert(ctr_f == 43);
    
    free(ctr);
    
    return 0;
}
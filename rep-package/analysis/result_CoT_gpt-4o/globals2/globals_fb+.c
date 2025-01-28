#include "stdlib.h"
#include "limits.h"
// Forward declaration of predicates
//predicate counter_f(struct counter* ctr, int v);

struct counter {
    int f;
};

// Global declarations
static int x;
static struct counter *c;

// Predicate definition for struct field access
// predicate counter_f(struct counter* ctr, int v) = ctr->f |-> v;

void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v) &*& v >= INT_MIN &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

int main() //@ : main_full(globals_fb+)
//@ requires module(globals_fb+, true);
//@ ensures true;
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    // @ close counter_f(ctr, _); // Close the counter predicate initially
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    //@ close counter_f(ctr, ctr->f); // Close the counter predicate with field value
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ open counter_f(ctr, ctr_f); // Open predicate before free
    free(ctr);
    return 0;
    //@ leak integer(&x, _) &*& pointer(&c, _);
}
#include "stdlib.h"

/*@
// Predicate for a counter struct, holding its field and malloc_block.
// The parameter 'v' represents the value of the field 'f'.
predicate counter_f(struct counter *c; int v) =
    c->f |-> v &*&
    malloc_block_counter(c);

// Predicate for the global variables 'x' and 'c'.
predicate globals() = x |-> _ &*& c |-> _;

// Predicate family instances for the main module, which manages the globals.
// 'main_pre' specifies the resources the module provides at the start.
predicate_family_instance main_pre(globals_main_fbp)() = globals();
// 'main_post' is what 'close_module' would require. Since 'main_full' ensures 'junk()',
// we don't need to close the module, so 'true' is sufficient.
predicate_family_instance main_post(globals_main_fbp)() = true;
@*/

static int x;

struct counter {
    int f;
};

static struct counter *c;


void m()
//@ requires x |-> 7 &*& c |-> ?ctr &*& counter_f(ctr, ?v) &*& v >= INT_MIN &*& v + 1 <= INT_MAX;
//@ ensures x |-> 8 &*& c |-> ctr &*& counter_f(ctr, v + 1);
{
    //@ open counter_f(ctr, v);
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
    //@ close counter_f(ctr, v + 1);
}


// TODO: make this function pass the verification
int main() //@ : main_full(globals_main_fbp)
//@ requires module(globals_main_fbp, true);
//@ ensures true;
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    //@ close counter_f(ctr, 42);
    c = ctr;
    m();
    //@ open counter_f(ctr, 43);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    free(ctr);
    return 0;
}
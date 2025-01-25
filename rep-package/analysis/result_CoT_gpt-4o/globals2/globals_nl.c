#include "stdlib.h"
//#include "verifast.h"

static int x;

struct counter {
    int f;
};

// Predicate to describe the state of a counter object
/*@
predicate counter(struct counter *c; int f) =
    c != 0 &*& c->f |-> f;

// Predicate to describe globally accessible structure 'c'
predicate global_counter(struct counter *ctr, int f) =
    c |-> ctr &*& counter(ctr, f);

// Predicates for global integer x
predicate global_x(int gx) =
    integer(&x, gx);
@*/

static struct counter *c;

/***
 * Description:
The m function updates the value of a global variable x and also increments the value of a field f within a global structure c.
*/

void m()
//@ requires global_counter(?ctr, ?f) &*& global_x(?gx) &*& gx + 1 >= INT_MIN &*& gx + 1 <= INT_MAX &*& f + 1 <= INT_MAX;
//@ ensures global_counter(ctr, f + 1) &*& global_x(gx + 1);
{
    //@ open global_counter(ctr, f);
    //@ open global_x(gx);
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
    //@ close global_counter(ctr, f + 1);
    //@ close global_x(gx + 1);
}

/***
 * Description:
The main function serves as the entry point of the program and allocates memory for a global structure, 
initializes its field f, assigns this structure to a global pointer c, 
calls the m() function, and performs validation on the updated value of field f.
*/

int main() //@ : main_full(globals_n)
//@ requires module(globals_n, true);
//@ ensures emp;
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    // @ close counter(ctr, _);
    ctr->f = 42;
    c = ctr;
    //@ close global_counter(_, _);
    //@ close global_x(_);
    m();
    //@ open global_counter(_, _);
    int ctr_f = c->f;
    assert(ctr_f == 43);
    //@ open counter(ctr, _);
    free(ctr);
    return 0;
    //@ leak global_x(_) &*& pointer(&c, _);
}

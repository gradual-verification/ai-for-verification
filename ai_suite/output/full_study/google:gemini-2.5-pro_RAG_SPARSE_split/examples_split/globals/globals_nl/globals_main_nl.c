#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

/*@
// Predicate for the global variables 'x' and 'c'.
predicate globals(int x_val, struct counter *c_ptr) =
    integer(&x, x_val) &*&
    pointer(&c, c_ptr);

// Predicate for the initial state of the globals.
predicate globals_init_pred() =
    globals(0, 0);

// Family instance for the main module's initial state.
predicate_family_instance module_init_pred(globals_main_nl)() = globals_init_pred();
@*/


/*** 
 * Description:
The m function updates the value of a global variable x and also increments the value of a field f within a global structure c.

It makes sure that the value of x and c->f are incremented by 1.
*/
void m()
    //@ requires globals(?x_val, ?c_ptr) &*& c_ptr != 0 &*& c_ptr->f |-> ?f_val;
    //@ ensures globals(x_val + 1, c_ptr) &*& c_ptr->f |-> (f_val + 1);
{
    //@ open globals(x_val, c_ptr);
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
    //@ close globals(x_val + 1, c_ptr);
}


// TODO: make this function pass the verification
/***
 * Description:
The main function tests the property of global variables. 
*/
int main() //@ : main_full(globals_main_nl)
    //@ requires module(globals_main_nl, true);
    //@ ensures true;
{
    //@ open_module();
    //@ open globals_init_pred();

    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;

    m();

    int ctr_f = ctr->f;
    assert(ctr_f == 43);

    free(ctr);

    return 0;
}
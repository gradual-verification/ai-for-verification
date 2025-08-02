#include "stdlib.h"

//@ #include "ghost_cells.gh"

static int x;

struct counter {
    int f;
};

static struct counter *c;

/*@
// Define predicates to track ownership of global variables
predicate globals_x(int value) = integer(&x, value);
predicate globals_c(struct counter *ptr) = pointer(&c, ptr);
predicate counter_f(struct counter *ptr, int value) = ptr->f |-> value &*& malloc_block_counter(ptr);

// Define a predicate for the main function's globals
predicate globals_main_nl() = true;

// Define a predicate for the state of all globals
predicate globals_state(int x_val, struct counter *c_ptr, int f_val) = 
    globals_x(x_val) &*& globals_c(c_ptr) &*& counter_f(c_ptr, f_val);
@*/

/*** 
 * Description:
The m function updates the value of a global variable x and also increments the value of a field f within a global structure c.

It makes sure that the value of x and c->f are incremented by 1.
*/
void m()
    //@ requires globals_x(?x_val) &*& globals_c(?c_ptr) &*& counter_f(c_ptr, ?f_val);
    //@ ensures globals_x(x_val + 1) &*& globals_c(c_ptr) &*& counter_f(c_ptr, f_val + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
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
    //@ open module(globals_main_nl, true);
    
    x = 7;
    //@ close globals_x(7);
    
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    //@ close counter_f(ctr, 42);
    
    c = ctr;
    //@ close globals_c(ctr);
    
    //@ assert globals_x(7) &*& globals_c(ctr) &*& counter_f(ctr, 42);
    
    m();
    
    //@ assert globals_x(8) &*& globals_c(ctr) &*& counter_f(ctr, 43);
    
    int ctr_f = ctr->f;
    //@ assert ctr_f == 43;
    
    assert(ctr_f == 43);
    
    //@ open globals_c(ctr);
    //@ open counter_f(ctr, 43);
    free(ctr);
    
    //@ open globals_x(8);
    
    return 0;
}
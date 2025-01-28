#include "stdlib.h"
#include "assert.h"

// Definition of a global integer.
static int x;

// Definition of a structure named counter.
struct counter {
    int f;
};

// Definition of a global pointer to a structure of type counter.
static struct counter *c;

/*@
predicate counter(struct counter *p, int f) =
    p != 0 &*& malloc_block_counter(p) &*& p->f |-> f;
@*/

/***
 * Description:
The m function updates the value of a global variable x and also increments the value of a field f within a global structure c.
*/

void m()
//@ requires c |-> ?ctr &*& counter(ctr, ?old_f) &*& ctr != 0 &*& integer(&x, ?val) &*& val + 1 >= INT_MIN &*& val + 1 <= INT_MAX &*& old_f + 1 <= INT_MAX;
//@ ensures c |-> ctr &*& counter(ctr, old_f + 1) &*& integer(&x, val + 1);
// Function body ensures the postcondition is fulfilled by reasoning about state changes.
{
    int y = x;
    x = y + 1;
    //@ open counter(ctr, old_f);
    c->f = c->f + 1;
    //@ close counter(ctr, old_f + 1);
}

/***
 * Description:
The main function serves as the entry point of the program and allocates memory for a global structure, 
initializes its field f, assigns this structure to a global pointer c, 
calls the m() function, and performs validation on the updated value of field f.
*/

int main() //@ : main_full(globals_nl)
//@ requires module(globals_nl, true);
//@ ensures true;
// Function involves memory allocation, state updates and condition checking.
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));

    if (ctr == 0) abort();
    
    ctr->f = 42;
    c = ctr;
    /*@
    close counter(c, 42);
    @*/
    m();
    /*@
    open counter(c, 43);
    @*/
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    
    free(ctr);

    return 0;
    //@ leak integer(&x, _) &*& pointer(&c, _);
}

#include "stdlib.h"
// #include "verifast.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

/*@ 
predicate counter(struct counter *c, int f) =
    c->f |-> f;
@*/

/*** 
 * Description:
The m function updates the value of a global variable x and also increments the value of a field f within a global structure c.
*/

void m()
//@ requires c |-> ?ctr &*& counter(ctr, ?fc) &*& integer(&x, 7) &*& fc + 1 <= INT_MAX;
//@ ensures c |-> ctr &*& counter(ctr, fc + 1) &*& integer(&x, 8);
{
    int y = x;
    x = y + 1;
    //@ open counter(ctr, fc);
    c->f = c->f + 1;
    //@ close counter(ctr, fc + 1);
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
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    
    ctr->f = 42;
    /*@ 
    close counter(ctr, 42); 
    @*/
    c = ctr;
    /* @ 
    open counter(c, 42); 
    @*/
    m();
    /*@
    open counter(c, _);
    @*/
    int ctr_f = ctr->f;
    //@ assert ctr_f == 43;
    free(ctr);
    return 0;
    //@ leak integer(&x, _) &*& pointer(&c, _);
}

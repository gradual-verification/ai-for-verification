#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

/***
 * Description:
The m function updates the value of a global variable x and also increments the value of a field f within a global structure c.

It makes sure that the value of x and c->f are incremented by 1.
*/
void m()
//@ requires integer(&x, ?vx) &*& c->f |-> ?vf &*& malloc_block_counter(c);
//@ ensures integer(&x, vx + 1) &*& c->f |-> vf + 1 &*& malloc_block_counter(c);
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
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    //@ close integer(&x, 7);
    //@ close malloc_block_counter(ctr);
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    free(ctr);
    //@ leak module(globals_main_nl, _);
    return 0;
}
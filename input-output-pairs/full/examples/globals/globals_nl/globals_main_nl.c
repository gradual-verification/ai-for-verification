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
{
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
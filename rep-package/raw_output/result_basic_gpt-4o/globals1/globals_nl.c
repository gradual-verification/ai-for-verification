#include "stdlib.h"
#include "verifast.h"

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
/*@
requires counter(c, ?fc);
ensures counter(c, fc + 1) &*& x == old_x + 1;
@*/
void m()
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

/***
 * Description:
The main function serves as the entry point of the program and allocates memory for a global structure, 
initializes its field f, assigns this structure to a global pointer c, 
calls the m() function, and performs validation on the updated value of field f.
*/
/*@
requires true;
ensures true;
@*/
int main()
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    /*@ 
    close counter(ctr, 42); 
    @*/
    ctr->f = 42;
    c = ctr;
    /*@ 
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
}

#include "stdlib.h"

// Global variables
static int x;

// Structure definition
struct counter {
    int f;
};

// Global pointer
static struct counter *c;

/*@
predicate counter(struct counter *ctr, int f) =
    ctr->f |-> f;
@*/

/*@ 
requires x == _ &*& c == _; // c and x can be accessed but are not owned
ensures x == _ &*& c == _;  // c and x can be accessed but are not owned
@*/
void m()
//@ requires [?f1]counter(c, ?f) &*& c != 0;
//@ ensures [f1]counter(c, f + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

/*@ 
requires true;
ensures true;
@*/
int main()
//@ requires true;
//@ ensures true;
{
    x = 7;

    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    //@ close counter(ctr, 42);
    ctr->f = 42;

    c = ctr;
    
    //@ open counter(c, 42);
    m();
    //@ open counter(c, 43);

    int ctr_f = ctr->f;
    //@ assert ctr_f == 43;

    //@ close counter(c, 43);
    free(ctr);

    return 0;
}

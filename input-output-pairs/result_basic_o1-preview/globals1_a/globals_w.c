#include "stdlib.h"

struct counter {
    int f;
};

static int x;
static struct counter *c;

/*@
predicate globals(int xv, struct counter* ctr) = integer(&x, xv) &*& pointer(&c, ctr);
predicate counter(struct counter* c, int v) = c->f |-> v;
@*/

void m()
//@ requires globals(7, ?ctr) &*& counter(ctr, ?v);
/*@ ensures globals(8, ctr) &*& counter(ctr, v + 1); @*/
{
    //@ open globals(7, ctr);
    //@ open integer(&x, 7);
    int y = x;
    x = y + 1;
    //@ close integer(&x, 8);
    //@ open counter(ctr, v);
    int fv = c->f;
    c->f = fv + 1;
    //@ close counter(ctr, v + 1);
    //@ close globals(8, ctr);
}

int main()
//@ requires true;
//@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    //@ close counter(ctr, 42);
    //@ close globals(7, ctr);
    m();
    //@ open counter(ctr, 43);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ open globals(8, ctr);
    //@ open counter(ctr, 43);
    free(ctr);
    return 0;
}

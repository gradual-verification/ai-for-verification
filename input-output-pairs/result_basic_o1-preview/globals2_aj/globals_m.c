#include "stdlib.h"

/*@
predicate globals_m() = x |-> ?xv &*& c |-> ?c_ptr &*& counter(c_ptr, ?cv);

predicate counter(struct counter *ctr; int v) = ctr->f |-> v;

@*/

static int x;
static struct counter *c;

struct counter {
    int f;
};

void m()
//@ requires globals_m() &*& x <= INT_MAX -1 &*& counter(c, ?cv) &*& cv <= INT_MAX -1;
//@ ensures globals_m();
{
    //@ open globals_m();
    int y = x;
    x = y + 1;
    c->f = c->f +1;
    //@ close counter(c, cv +1);
    //@ close globals_m();
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
    //@ close globals_m();
    m();
    //@ open globals_m();
    //@ open counter(ctr, ?ctr_f_val);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    free(ctr);
    return 0;
}

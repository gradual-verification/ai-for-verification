#include "stdlib.h"
/*@
predicate counter(struct counter *c, int f) =
    c != 0 &*& c->f |-> f;
@*/

static int x;
static struct counter *c;

struct counter {
    int f;
};

/*@
requires true;
ensures x == old_x + 1 &*& counter(c, old_f + 1) &*& old_x == *x &*& old_f == *f;
@*/
void m()
//@ requires counter(c, ?old_f) &*& c != 0;
//@ ensures counter(c, old_f + 1) &*& x == old_x + 1;
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

/*@
requires true;
ensures result == 0;
@*/
int main()
//@ requires true;
//@ ensures true;
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    //@ open malloc_block(ctr);
    ctr->f = 42;
    //@ close counter(ctr, 42);
    c = ctr;
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ open counter(ctr, 43);
    free(ctr);
    return 0;
}

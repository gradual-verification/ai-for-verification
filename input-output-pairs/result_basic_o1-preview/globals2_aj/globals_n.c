#include "stdlib.h"

/*@
predicate x(int v) = &x |-> v;
predicate c(struct counter *p) = &c |-> p;
predicate counter(struct counter *ctr; int f) =
    ctr->f |-> f;
@*/

static int x;
static struct counter *c;

struct counter {
    int f;
};

/*@
    requires x(?v) &*& c(?p) &*& counter(p, ?f);
    ensures x(v + 1) &*& c(p) &*& counter(p, f + 1);
@*/
void m()
{
    //@ open x(?v);
    //@ open c(?p);
    //@ open counter(p, ?f);
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
    //@ close counter(p, f + 1);
    //@ close c(p);
    //@ close x(v + 1);
}

/*@
    requires true;
    ensures true;
@*/
int main()
{
    //@ close x(7); // Initialize x predicate
    x = 7;

    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    //@ close counter(ctr, _); // Allocate counter predicate
    ctr->f = 42;
    //@ open counter(ctr, _);
    //@ close counter(ctr, 42);

    //@ close c(ctr); // Initialize c predicate
    c = ctr;

    /* Now we have:
     * x(7)
     * c(ctr)
     * counter(ctr, 42)
     */

    m(); // Requires x(?v), c(?p), counter(p, ?f)

    /* After m():
     * x(8)
     * c(ctr)
     * counter(ctr, 43)
     */

    //@ open counter(ctr, 43);
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ close counter(ctr, 43);

    //@ open counter(ctr, _); // Before freeing, open predicate
    free(ctr);

    return 0;
}

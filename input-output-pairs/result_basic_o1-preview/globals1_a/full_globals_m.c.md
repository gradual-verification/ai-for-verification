```c
#include "stdlib.h"

/*@

module g();

int x;
struct counter* c;

predicate counter(struct counter* c, int v) = c->f |-> v &*& malloc_block_counter(c);

predicate g::globals(int vx, struct counter* vc, int vf) = 
    integer(&x, vx) &*& c |-> vc &*& counter(vc, vf);

@*/

struct counter {
    int f;
};

static int x;
//@ global_variable int x;
static struct counter *c;
//@ global_variable struct counter* c;

void m()
//@ requires g::globals(?vx, ?vc, ?vf) &*& vf + 1 <= INT_MAX &*& vx + 1 <= INT_MAX;
//@ ensures g::globals(vx + 1, vc, vf + 1);
{
    //@ open g::globals(vx, vc, vf);
    int y = x;
    x = y + 1;
    vc->f = vc->f + 1;
    //@ close g::globals(vx + 1, vc, vf + 1);
}

int main() //@ : main_full(g)
//@ requires module(g, true);
//@ ensures true;
{
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    //@ close counter(ctr, 42);
    //@ open g::globals(_, _, _);
    x = 7;
    c = ctr;
    //@ close g::globals(7, ctr, 42);
    m();
    //@ open g::globals(?vx, ?vc, ?vf);
    int ctr_f = vc->f;
    assert(ctr_f == 43);
    //@ open counter(vc, vf);
    free(vc);
    return 0;
}
```

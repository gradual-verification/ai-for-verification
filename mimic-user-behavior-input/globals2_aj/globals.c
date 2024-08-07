#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

// uses heap chunk counter_f for verification which is not a predicate, globals1_a contains the predicate version
void m()
    //@ requires integer(&x, 7) &*& pointer(&c, ?ctr) &*& counter_f(ctr, ?v) &*& INT_MIN <= v &*& v + 1 <= INT_MAX;
    //@ ensures integer(&x, 8) &*& pointer(&c, ctr) &*& counter_f(ctr, v + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

int main() //@ : main_full(globals)
    //@ requires module(globals, true);
    //@ ensures true;
{
    //@ open_module();
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    ctr->f = 42;
    c = ctr;
    m();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    free(ctr);
    //@ leak integer(&x, _) &*& pointer(&c, _);
    return 0;
}
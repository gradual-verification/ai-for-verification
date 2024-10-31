```c
#include "stdlib.h"

static int x;

struct counter {
    int f;
};

//@ predicate counter(struct counter *ctr; int v) = ctr->f |-> v;

static struct counter *c;

/*@

predicate module_state(int x_value, struct counter *ctr, int ctr_f_value) =
    x |-> x_value &*& c |-> ctr &*& (ctr != 0 ? counter(ctr, ctr_f_value) : true);

@*/

void m()
//@ requires module_state(?x_value, ?ctr, ?ctr_f_value);
//@ ensures module_state(x_value + 1, ctr, ctr_f_value + 1);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
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
    //@ close module_state(7, ctr, 42);

    m();

    //@ open module_state(?x_value_after_m, ?ctr_after_m, ?ctr_f_value_after_m);

    int ctr_f = ctr->f;
    assert(ctr_f == 43);

    c = 0;
    //@ c |-> 0;

    //@ close module_state(x_value_after_m, 0, 0);
    //@ open module_state(_, _, _);

    //@ open counter(ctr, _);
    free(ctr);

    return 0;
}
```

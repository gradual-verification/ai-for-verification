```c
#include "stdlib.h"

/*@
predicate x(int value) =
    &x |-> value;

predicate c_ptr(struct counter *ctr) =
    &c |-> ctr;

predicate counter(struct counter *ctr; int f) =
    ctr != 0 &*&
    ctr->f |-> f &*&
    malloc_block_counter(ctr);

predicate malloc_block_counter(struct counter *ctr) = 
    malloc_block(ctr, sizeof(struct counter));

@*/

static int x;
static struct counter *c;

struct counter {
    int f;
};

/*@
requires x(?x_value) &*& c_ptr(?ctr) &*& counter(ctr, ?f_value);
ensures x(x_value + 1) &*& c_ptr(ctr) &*& counter(ctr, f_value + 1);
@*/
void m()
{
    //@ open x(x_value);
    int y = x;
    x = y + 1;
    //@ close x(x_value + 1);

    //@ open c_ptr(ctr);
    //@ open counter(ctr, f_value);
    c->f = c->f + 1;
    //@ close counter(ctr, f_value + 1);
    //@ close c_ptr(ctr);
}

/*@
requires true;
ensures true;
@*/
int main()
{
    x = 7;
    //@ close x(7);

    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    //@ close malloc_block_counter(ctr);
    ctr->f = 42;

    //@ close counter(ctr, 42);
    c = ctr;
    //@ close c_ptr(ctr);

    m();

    //@ open counter(ctr, ?ctr_f);
    int ctr_f = ctr->f;
    //@ assert ctr_f == 43;
    //@ close counter(ctr, ctr_f);

    //@ open c_ptr(ctr);
    //@ open x(?x_value);

    //@ open counter(ctr, ctr_f);
    //@ open malloc_block_counter(ctr);
    free(ctr);
    return 0;
}
```

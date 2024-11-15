#include "stdlib.h"
#include "verifast.h"

static int x;

struct counter {
    int f;
};

// Predicate to describe the state of a counter object
predicate counter(struct counter *c;) =
    c != 0 &*& c->f |-> ?f;

// Predicate to describe globally accessible structure 'c'
predicate global_counter() =
    counter(c);

// Predicates for global integer x
predicate global_x() =
    [1/2]integer(&x, ?gx);

static struct counter *c;

/***
 * Description:
The m function updates the value of a global variable x and also increments the value of a field f within a global structure c.
*/
/*@
requires
  global_counter() &*&
  global_x();
ensures
  global_counter() &*&
  global_x();
@*/
void m()
{
    //@ open global_counter();
    //@ open global_x();
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
    //@ close global_counter();
    //@ close global_x();
}

/***
 * Description:
The main function serves as the entry point of the program and allocates memory for a global structure, 
initializes its field f, assigns this structure to a global pointer c, 
calls the m() function, and performs validation on the updated value of field f.
*/
/*@
requires
  true;
ensures
  emp;
@*/
int main()
{
    x = 7;
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    //@ close counter(ctr);
    ctr->f = 42;
    c = ctr;
    //@ close global_counter();
    //@ close global_x();
    m();
    //@ open global_counter();
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    //@ open counter(ctr);
    free(ctr);
    return 0;
}

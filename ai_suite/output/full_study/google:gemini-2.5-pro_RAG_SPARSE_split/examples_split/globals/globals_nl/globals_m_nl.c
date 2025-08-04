#include "stdlib.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;


// TODO: make this function pass the verification
/*** 
 * Description:
The m function updates the value of a global variable x and also increments the value of a field f within a global structure c.

It makes sure that the value of x and c->f are incremented by 1.
*/
/*@
requires
    x |-> ?v_x &*& v_x < INT_MAX &*&
    c |-> ?c_ptr &*&
    c_ptr->f |-> ?v_f &*& v_f < INT_MAX;
ensures
    x |-> v_x + 1 &*&
    c |-> c_ptr &*&
    c_ptr->f |-> v_f + 1;
@*/
void m()
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}
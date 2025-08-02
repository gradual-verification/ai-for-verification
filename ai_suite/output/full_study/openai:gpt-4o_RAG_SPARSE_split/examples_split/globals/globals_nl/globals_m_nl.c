#include "stdlib.h"

// Global variables
static int x;
struct counter {
    int f;
};
static struct counter *c;

// TODO: make this function pass the verification
/*** 
 * Description:
 * The m function updates the value of a global variable x and also increments the value of a field f within a global structure c.
 * It makes sure that the value of x and c->f are incremented by 1.
 */
//@ requires integer(&x, ?vx) &*& c != 0 &*& c->f |-> ?vf;
//@ ensures integer(&x, vx + 1) &*& c->f |-> vf + 1;
void m()
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}
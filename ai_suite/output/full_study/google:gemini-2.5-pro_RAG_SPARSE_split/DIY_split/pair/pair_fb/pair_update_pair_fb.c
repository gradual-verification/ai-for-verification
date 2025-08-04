#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    p->x |-> x &*& p->y |-> y;
@*/

void update_pair(struct pair *p, int new_x, int new_y)
    //@ requires pair(p, _, _);
    //@ ensures pair(p, new_x, new_y);
{
    p->x = new_x;
    p->y = new_y;
}
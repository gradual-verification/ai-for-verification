#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    malloc_block_pair(p) &*& p->x |-> x &*& p->y |-> y;
@*/

// TODO: make this function pass the verification
struct pair* copy_pair(struct pair *p)
    //@ requires pair(p, ?x, ?y);
    //@ ensures pair(p, x, y) &*& result != 0 &*& pair(result, x, y);
{
    struct pair* new_p = malloc(sizeof(struct pair));
    //@ open pair(p, x, y);
    if (new_p == 0) abort();
    new_p->x = p->x;
    new_p->y = p->y;
    //@ close pair(p, x, y);
    //@ close pair(new_p, x, y);
    return new_p;
}
#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    p->x |-> x &*& p->y |-> y &*& malloc_block_pair(p);
@*/

// TODO: make this function pass the verification
struct pair* create_pair(int x, int y)
    //@ requires true;
    //@ ensures pair(result, x, y);
{
    struct pair* p = malloc(sizeof(struct pair));
    if (p == 0) abort();
    p->x = x;
    p->y = y;
    //@ close pair(p, x, y);
    return p;
}
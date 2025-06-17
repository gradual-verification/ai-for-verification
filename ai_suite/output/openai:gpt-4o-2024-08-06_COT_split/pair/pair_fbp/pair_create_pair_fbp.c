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
struct pair* create_pair(int x, int y)
    //@ requires true;
    //@ ensures result != 0 ? pair(result, x, y) : true;
{
    struct pair* p = malloc(sizeof(struct pair));
    //@ open exists<int>(sizeof(struct pair));
    if (p == 0) abort();
    //@ open malloc_block(p, sizeof(struct pair));
    p->x = x;
    p->y = y;
    //@ close pair(p, x, y);
    return p;
}
#include "stdlib.h"

struct pair {
    int x;
    int y;
};

//@ predicate pair(struct pair *p; int x, int y) = p->x |-> x &*& p->y |-> y &*& malloc_block_pair(p);

struct pair* copy_pair(struct pair *p)
    //@ requires pair(p, ?x, ?y);
    //@ ensures pair(result, x, y);
{
    struct pair* new_p = malloc(sizeof(struct pair));
    if (new_p == 0) abort();
    new_p->x = p->x;
    new_p->y = p->y;
    //@ close pair(new_p, x, y);
    return new_p;
}
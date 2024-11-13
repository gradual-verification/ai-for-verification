```c
#include "stdlib.h"
#include "stdbool.h"

// Definition of predicates
//@ predicate malloc_block_point(struct point *p) = malloc_block(p, sizeof(struct point));

void swap(int *a, int *b)
//@ requires integer(a, ?x) &*& integer(b, ?y);
//@ ensures integer(a, y) &*& integer(b, x);
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

struct point {
    int x;
    int y;
};

void point_mirror(struct point *p)
//@ requires p->x |-> ?x &*& p->y |-> ?y;
//@ ensures p->x |-> y &*& p->y |-> x;
{
    swap(&p->x, &p->y);
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ open malloc_block_point(p);
    //@ close p->x |-> _;
    //@ close p->y |-> _;
    p->x = 3;
    p->y = 10;
    //@ open p->x |-> _;
    //@ open p->y |-> _;
    point_mirror(p);
    //@ close p->x |-> _;
    //@ close p->y |-> _;
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    //@ open malloc_block_point(p);
    free(p);
    return 0;
}
```

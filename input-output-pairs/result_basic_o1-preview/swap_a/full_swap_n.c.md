```c
#include "stdlib.h"
#include "stdbool.h"

/*@
predicate point(struct point *p; int x, int y) =
    p->x |-> x &*& p->y |-> y &*& malloc_block_point(p);
@*/

struct point {
    int x;
    int y;
};

void swap(int *a, int *b)
    //@ requires integer(a, ?va) &*& integer(b, ?vb);
    //@ ensures integer(a, vb) &*& integer(b, va);
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

void point_mirror(struct point *p)
    //@ requires point(p, ?x, ?y);
    //@ ensures point(p, y, x);
{
    //@ open point(p, x, y);
    swap(&p->x, &p->y);
    //@ close point(p, y, x);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ close malloc_block_point(p);
    //@ p->x |-> _;
    //@ p->y |-> _;
    p->x = 3;
    p->y = 10;
    //@ close point(p, 3, 10);
    point_mirror(p);
    //@ open point(p, 10, 3);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    //@ open point(p, 10, 3);
    //@ p->x |-> _;
    //@ p->y |-> _;
    //@ open malloc_block_point(p);
    free(p);
    return 0;
}
```

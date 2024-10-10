#include "stdlib.h"
#include <stdbool.h>

// Swap function with refined specs for VeriFast
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

// Point mirror function with specs for VeriFast
void point_mirror(struct point *p)
    //@ requires struct_point_padding(p) &*& integer(&p->x, ?x) &*& integer(&p->y, ?y);
    //@ ensures struct_point_padding(p) &*& integer(&p->x, y) &*& integer(&p->y, x);
{
    swap(&p->x, &p->y);
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ open_struct_point(p);
    //@ assert struct_point_padding(p);
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    bool b = (p->x == 10) && (p->y == 3);
    assert(b);
    //@ close_struct_point(p);
    free(p);
    return 0;
}
//@ predicate struct_point_padding(struct point *p) = true;

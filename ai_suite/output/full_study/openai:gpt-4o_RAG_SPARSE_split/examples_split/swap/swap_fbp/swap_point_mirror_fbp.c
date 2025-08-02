#include "stdlib.h"

struct point {
    int x;
    int y;
};

void swap(int *a, int *b)
//@ requires integer(a, ?x) &*& integer(b, ?y);
//@ ensures integer(a, y) &*& integer(b, x);
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

// TODO: make this function pass the verification
void point_mirror(struct point *p)
//@ requires p->x |-> ?x &*& p->y |-> ?y;
//@ ensures p->x |-> y &*& p->y |-> x;
{
    //@ open_struct(p);
    swap(&p->x, &p->y);
    //@ close_struct(p);
}
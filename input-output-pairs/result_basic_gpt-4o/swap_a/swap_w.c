#include "stdlib.h"
#include <stdbool.h>

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
//@ requires struct_point(p, ?x, ?y);
//@ ensures struct_point(p, y, x);
{
    //@ open struct_point(p, x, y);
    swap(&p->x, &p->y);
    //@ close struct_point(p, y, x);
}

lemma void struct_point_unique(struct point* p)
//@ requires struct_point(p, ?x, ?y) &*& struct_point(p, ?x2, ?y2);
//@ ensures false;
{
    //@ open struct_point(p, x, y);
    //@ open struct_point(p, x2, y2);
    //@ assert x == x2 && y == y2;
}

predicate struct_point(struct point *p; int x, int y) =
    p->x |-> x &*& p->y |-> y;

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ close struct_point(p, 3, 10);
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    //@ open struct_point(p, 10, 3);
    bool b = (p->x == 10) && (p->y == 3);
    assert(b);
    free(p);
    return 0;
}

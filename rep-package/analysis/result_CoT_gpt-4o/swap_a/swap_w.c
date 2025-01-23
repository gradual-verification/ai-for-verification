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

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    
    // @ close struct_point(p, 0, 0);
    p->x = 3;
    p->y = 10;
    //@ open struct_point(p, _, _);
    //@ close struct_point(p, p->x, p->y);

    point_mirror(p);
    
    //@ open struct_point(p, _, _);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    
    //@ open struct_point(p, _, _);
    free(p);
    return 0;
}

//@ predicate struct_point(struct point *p; int x, int y) = p->x |-> x &*& p->y |-> y;

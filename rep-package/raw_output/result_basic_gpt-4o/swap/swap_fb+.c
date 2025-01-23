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
//@ requires struct_point(p, ?v);
//@ ensures struct_point(p, pair(snd(v), fst(v)));
{
    //@ open struct_point(p, v);
    swap(&p->x, &p->y);
    //@ close struct_point(p, pair(snd(v), fst(v)));
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ close struct_point(p, pair(?x, ?y));
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    //@ open struct_point(p, _);
    free(p);
    return 0;
}

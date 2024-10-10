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
//@ requires p->x |-> ?x &*& p->y |-> ?y;
//@ ensures p->x |-> y &*& p->y |-> x;
{
    //@ open p->x |-> x &*& p->y |-> y;
    swap(&p->x, &p->y);
    //@ close p->x |-> y &*& p->y |-> x;
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ close p->x |-> 3 &*& p->y |-> 10;
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    //@ open p->x |-> 10 &*& p->y |-> 3;
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    free(p);
    return 0;
}

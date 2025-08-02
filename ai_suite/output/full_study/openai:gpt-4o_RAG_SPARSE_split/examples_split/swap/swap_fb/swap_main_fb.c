#include "stdlib.h"

struct point {
    int x;
    int y;
};

void swap(int *a, int *b)
//@ requires *a |-> ?x &*& *b |-> ?y;
//@ ensures *a |-> y &*& *b |-> x;
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

void point_mirror(struct point *p)
//@ requires p->x |-> ?x &*& p->y |-> ?y;
//@ ensures p->x |-> y &*& p->y |-> x;
{
    swap(&p->x, &p->y);
}

// TODO: make this function pass the verification
int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ assume(p != 0);
    //@ close_struct(p);
    p->x = 3;
    p->y = 10;
    //@ open_struct(p);
    point_mirror(p);
    //@ open_struct(p);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    //@ close_struct(p);
    free(p);
    return 0;
}
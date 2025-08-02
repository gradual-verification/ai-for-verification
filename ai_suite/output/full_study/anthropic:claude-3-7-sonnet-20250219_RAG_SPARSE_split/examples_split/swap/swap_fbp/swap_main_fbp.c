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
    //@ assert p != 0;
    //@ assert malloc_block(p, sizeof(struct point));
    
    p->x = 3;
    p->y = 10;
    //@ assert p->x |-> 3;
    //@ assert p->y |-> 10;
    
    point_mirror(p);
    //@ assert p->x |-> 10;
    //@ assert p->y |-> 3;
    
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    
    free(p);
    return 0;
}
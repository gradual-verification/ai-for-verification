#include "stdlib.h"

struct point {
    int x;
    int y;
};

// TODO: make this function pass the verification
void swap(int *a, int *b)
//@ requires integer(a, ?x) &*& integer(b, ?y);
//@ ensures integer(a, y) &*& integer(b, x);
{
    int tmp = *a;
    //@ integer_limits(a);
    //@ integer_limits(b);
    *a = *b;
    *b = tmp;
}
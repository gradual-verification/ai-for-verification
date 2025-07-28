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
    *a = *b;
    *b = tmp;
}


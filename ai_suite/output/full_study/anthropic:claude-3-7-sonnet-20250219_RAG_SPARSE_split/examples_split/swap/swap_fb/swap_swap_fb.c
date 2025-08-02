#include "stdlib.h"

struct point {
    int x;
    int y;
};


// TODO: make this function pass the verification
void swap(int *a, int *b)
//@ requires *a |-> ?x &*& *b |-> ?y;
//@ ensures *a |-> y &*& *b |-> x;
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}
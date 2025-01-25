#include "stdlib.h"
#include <stdbool.h>

// Swap function: Swaps the values of two integers.
void swap(int *a, int *b)
//@ requires integer(a, ?x) &*& integer(b, ?y);
//@ ensures integer(a, y) &*& integer(b, x);
{
    // The function swaps the integers pointed by 'a' and 'b'.
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

// Define structure 'point' to represent a point with coordinates (x, y).
struct point {
    int x;
    int y;
};

// Point mirror function: Mirrors a point by swapping its x and y coordinates.
void point_mirror(struct point *p)
//@ requires p->x |-> ?x &*& p->y |-> ?y;
//@ ensures p->x |-> y &*& p->y |-> x;
{
    // The function uses 'swap' to exchange the x and y values of a point.
    swap(&p->x, &p->y);
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    // Allocate memory for a point structure.
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    
    // Assign initial values to point coordinates.
    p->x = 3;
    p->y = 10;
    
    // Mirror the point by swapping its coordinates.
    point_mirror(p);
    
    // Assert that the coordinates have been correctly swapped.
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    
    // Free the allocated memory.
    free(p);
    return 0;
}

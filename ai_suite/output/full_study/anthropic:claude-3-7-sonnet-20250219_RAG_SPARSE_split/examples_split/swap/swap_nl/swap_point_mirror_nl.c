#include "stdlib.h"

struct point {
    int x;
    int y;
};

/*** 
 * Description:
The swap function takes two integer pointers as parameters and swaps the values they point to.

@param a - Pointer to the first integer value to be swapped.
@param b - Pointer to the second integer value to be swapped.

It makes sure that the values pointed to by a and b are swapped correctly.
*/
void swap(int *a, int *b)
//@ requires integer(a, ?va) &*& integer(b, ?vb);
//@ ensures integer(a, vb) &*& integer(b, va);
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

// TODO: make this function pass the verification
/*** 
 * Description:
The point_mirror function takes a pointer to a struct point as a parameter and swaps the x and y values of the point.

@param p - Pointer to the struct point whose x and y values need to be swapped.

It makes sure that the x and y values of the point are swapped correctly.
*/
void point_mirror(struct point *p)
//@ requires p->x |-> ?x &*& p->y |-> ?y;
//@ ensures p->x |-> y &*& p->y |-> x;
{
    swap(&p->x, &p->y);
}
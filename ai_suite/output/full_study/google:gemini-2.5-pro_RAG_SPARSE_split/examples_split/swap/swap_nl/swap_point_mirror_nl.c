#include "stdlib.h"

struct point {
    int x;
    int y;
};

/*@
predicate point(struct point *p; int x, int y) =
    p->x |-> x &*&
    p->y |-> y &*&
    malloc_block_point(p);
@*/


/*** 
 * Description:
The swap function takes two integer pointers as parameters and swaps the values they point to.

@param a - Pointer to the first integer value to be swapped.
@param b - Pointer to the second integer value to be swapped.

It makes sure that the values pointed to by a and b are swapped correctly.
*/
/*@
requires integer(a, ?val_a) &*& integer(b, ?val_b);
ensures integer(a, val_b) &*& integer(b, val_a);
@*/
void swap(int *a, int *b)
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
/*@
requires point(p, ?x_val, ?y_val);
ensures point(p, y_val, x_val);
@*/
void point_mirror(struct point *p)
{
    swap(&p->x, &p->y);
}
#include "stdlib.h"
#include "stdbool.h"
#include "assert.h"

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
    //@ requires integer(a, ?val_a) &*& integer(b, ?val_b);
    //@ ensures integer(a, val_b) &*& integer(b, val_a);
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}



/*** 
 * Description:
The point_mirror function takes a pointer to a struct point as a parameter and swaps the x and y values of the point.

@param p - Pointer to the struct point whose x and y values need to be swapped.

It makes sure that the x and y values of the point are swapped correctly.
*/
void point_mirror(struct point *p)
    //@ requires point(p, ?x, ?y);
    //@ ensures point(p, y, x);
{
    //@ open point(p, x, y);
    swap(&p->x, &p->y);
    //@ close point(p, y, x);
}


// TODO: make this function pass the verification
/*** 
 * Description: 
The main function checks if the mirror operation is successful.
*/
int main()
    //@ requires true;
    //@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    p->x = 3;
    p->y = 10;
    
    //@ close point(p, 3, 10);
    
    point_mirror(p);
    
    //@ open point(p, 10, 3);
    
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    
    free(p);
    
    return 0;
}
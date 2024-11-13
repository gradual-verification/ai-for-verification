#include "stdlib.h"
#include <stdbool.h>

/*@
predicate point(struct point *p; int x, int y) =
    malloc_block_point(p) &*& p->x |-> x &*& p->y |-> y;
@*/

/*** 
 * Description:
 * The swap function takes two integer pointers as parameters and swaps the values they point to.
 *
 * @param a - Pointer to the first integer value to be swapped.
 * @param b - Pointer to the second integer value to be swapped.
 */
/*@ 
requires a != 0 &*& b != 0 &*& *a |-> _ &*& *b |-> _;
ensures  *a |-> old_int(*b) &*& *b |-> old_int(*a);
@*/
void swap(int *a, int *b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

struct point {
    int x;
    int y;
};

/*** 
 * Description:
 * The point_mirror function takes a pointer to a struct point as a parameter and swaps the x and y values of the point.
 *
 * @param p - Pointer to the struct point whose x and y values need to be swapped.
 */
/*@ 
requires point(p, ?x, ?y);
ensures  point(p, y, x);
@*/
void point_mirror(struct point *p)
{
    /*@ open point(p, ?x, ?y); @*/
    swap(&p->x, &p->y);
    /*@ close point(p, y, x); @*/
}

/*** 
 * Description: 
 * The main function of the program that allocates memory for a struct point, initializes its x and y values, 
 * mirrors the point, checks if the mirror operation was successful, and frees the allocated memory before exiting.
 */
/*@ 
requires true;
ensures true;
@*/
int main()
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    /*@ assume(malloc_block_point(p)); @*/
    /*@ close point(p, 3, 10); @*/
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    /*@ open point(p, 10, 3); @*/
    free(p);
    return 0;
}

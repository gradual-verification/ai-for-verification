#include "stdlib.h"

struct point {
    int x;
    int y;
};



/*** 
 * Description:
The point_mirror function takes a pointer to a struct point as a parameter and swaps the x and y values of the point.

@param p - Pointer to the struct point whose x and y values need to be swapped.

It makes sure that the x and y values of the point are swapped correctly.
*/
void point_mirror(struct point *p)
{
    swap(&p->x, &p->y);
}


// TODO: make this function pass the verification
/*** 
 * Description: 
The main function checks if the mirror operation is successful.
*/
int main()
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    free(p);
    return 0;
}
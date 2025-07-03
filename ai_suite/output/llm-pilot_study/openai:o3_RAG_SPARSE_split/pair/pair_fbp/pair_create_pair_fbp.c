#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    // ownership of the memory block itself
    malloc_block_pair(p)                        &*&
    // ownership of the two struct fields
    p->x |-> x                                  &*&
    p->y |-> y                                  &*&
    // (possible) padding bytes belonging to the struct
    struct_pair_padding(p);
@*/

// verified constructor
struct pair* create_pair(int x, int y)
    //@ requires true;
    //@ ensures  pair(result, x, y);
{
    struct pair *p = malloc(sizeof(struct pair));
    if (p == 0) abort();

    /* After the malloc we own:
         chars_(p, sizeof(struct pair), _)  &*&  malloc_block_pair(p)
       Writing to the fields transforms (part of) the chars_ chunk into the
       required field chunks automatically, while the remaining bytes (if any)
       are represented by struct_pair_padding(p). */

    p->x = x;
    p->y = y;

    //@ close pair(p, x, y);
    return p;
}
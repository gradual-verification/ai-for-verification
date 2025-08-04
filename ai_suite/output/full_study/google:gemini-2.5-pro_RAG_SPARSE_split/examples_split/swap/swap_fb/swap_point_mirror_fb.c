#include "stdlib.h"

struct point {
    int x;
    int y;
};

/*@
// A predicate that describes a point struct and its contents.
// 'p' is the pointer to the struct.
// 'x' and 'y' are the logical values of the fields.
predicate point(struct point *p; int x, int y) =
    // The 'x' field of the struct at 'p' has value 'x'.
    p->x |-> x &*&
    // The 'y' field of the struct at 'p' has value 'y'.
    p->y |-> y &*&
    // This represents ownership of any padding bytes in the struct,
    // ensuring full ownership.
    struct_point_padding(p);
@*/

void swap(int *a, int *b)
//@ requires *a |-> ?x &*& *b |-> ?y;
//@ ensures *a |-> y &*& *b |-> x;
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}


// TODO: make this function pass the verification
void point_mirror(struct point *p)
//@ requires point(p, ?x, ?y);
//@ ensures point(p, y, x);
{
    // To access the fields of the struct, we must first "open" the predicate.
    // This consumes the 'point(p, x, y)' chunk and produces the chunks for its fields.
    //@ open point(p, x, y);

    // Now we have p->x |-> x and p->y |-> y, which satisfies the precondition of swap.
    swap(&p->x, &p->y);
    // After swap, we have p->x |-> y and p->y |-> x.

    // To re-establish the 'point' predicate for the postcondition, we "close" it.
    // This consumes the field chunks and produces the 'point(p, y, x)' chunk.
    //@ close point(p, y, x);
}
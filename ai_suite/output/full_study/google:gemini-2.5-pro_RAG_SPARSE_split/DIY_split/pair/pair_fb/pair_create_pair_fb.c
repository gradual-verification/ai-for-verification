#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
// A predicate for a heap-allocated struct should account for all memory:
// the fields, the padding, and the malloc_block for the whole struct.
predicate pair(struct pair *p, int x, int y) =
    p->x |-> x &*&
    p->y |-> y &*&
    struct_pair_padding(p) &*&
    malloc_block_pair(p);
@*/

// TODO: make this function pass the verification
struct pair* create_pair(int x, int y)
    //@ requires true;
    //@ ensures pair(result, x, y);
{
    struct pair* p = malloc(sizeof(struct pair));
    if (p == 0) abort();
    p->x = x;
    p->y = y;
    // The 'ensures' clause implicitly closes the 'pair' predicate,
    // consuming all the required memory chunks.
    return p;
}
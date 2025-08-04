#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
    void ** data;
    int size;
    int capacity;
};

/*@
// It's good practice to define a helper predicate for the struct's malloc_block.
predicate malloc_block_arraylist(struct arraylist *a) =
    malloc_block(a, sizeof(struct arraylist));

predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*& malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity) &*& data[0..size] |-> vs &*& data[size..capacity] |-> _;
@*/


// This function already passes verification with the provided contract.
// The auto-lemma `pointers_inv` from the prelude establishes that `size == length(vs)`.
int list_length(struct arraylist * a)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, vs) &*& result == length(vs);
{
    return a->size;
}
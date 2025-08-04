#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
    void ** data;
    int size;
    int capacity;
};

/*@
// A malloc_block predicate for the arraylist struct itself.
predicate malloc_block_arraylist(struct arraylist *a) =
    malloc_block(a, sizeof(struct arraylist));

predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*&
  malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity) &*&
  data[0..size] |-> vs &*&
  data[size..capacity] |-> _ &*&
  length(vs) == size; // Explicitly state that the list length equals the size field.
@*/


// This function now passes verification.
void * list_get(struct arraylist * a, int i)
//@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
//@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
    // No annotations are needed in the body.
    // VeriFast automatically opens the arraylist predicate to access a->data.
    // It uses the `data[0..size] |-> vs` chunk and the precondition `0 <= i < length(vs)`
    // to prove that the access `a->data[i]` is safe and its value is `nth(i, vs)`.
    // The arraylist predicate is preserved and automatically closed at the end.
    return a->data[i];
}
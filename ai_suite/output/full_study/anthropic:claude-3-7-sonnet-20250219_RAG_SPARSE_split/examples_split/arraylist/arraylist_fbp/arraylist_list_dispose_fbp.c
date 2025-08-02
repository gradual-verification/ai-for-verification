#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
    void ** data;
    int size;
    int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*& malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity) &*& data[0..size] |-> vs &*& data[size..capacity] |-> _;
@*/


// TODO: make this function pass the verification
void list_dispose(struct arraylist * a)
//@ requires arraylist(a, ?vs);
//@ ensures true;
{
    //@ open arraylist(a, vs);
    void ** data = a -> data;
    int size = a -> size;
    int capacity = a -> capacity;
    
    //@ assert data[0..size] |-> vs;
    //@ assert data[size..capacity] |-> _;
    //@ assert malloc_block_pointers(data, capacity);
    
    free(data);
    free(a);
}
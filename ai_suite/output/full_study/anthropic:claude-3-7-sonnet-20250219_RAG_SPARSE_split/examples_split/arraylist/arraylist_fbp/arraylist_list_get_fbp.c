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
void * list_get(struct arraylist * a, int i)
//@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
//@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
    //@ open arraylist(a, vs);
    //@ assert a->data |-> ?data;
    //@ assert a->size |-> ?size;
    //@ assert a->capacity |-> ?capacity;
    //@ assert data[0..size] |-> vs;
    
    void* result = a->data[i];
    
    //@ close arraylist(a, vs);
    return result;
}
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
struct arraylist * create_arraylist()
//@ requires true;
//@ ensures arraylist(result, nil);
{
    struct arraylist * a = malloc(sizeof(struct arraylist));
    void * data = 0;
    if (a == 0) abort();
    a -> size = 0;
    data = malloc(100 * sizeof(void * ));
    if (data == 0) abort();
    a -> data = data;
    a -> capacity = 100;
    return a;
}


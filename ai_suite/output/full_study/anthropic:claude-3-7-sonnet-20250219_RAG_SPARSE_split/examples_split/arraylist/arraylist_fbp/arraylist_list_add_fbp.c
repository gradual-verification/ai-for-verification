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
void list_add(struct arraylist * a, void * v)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, append(vs, cons(v, nil)));
{
    //@ open arraylist(a, vs);
    int size = 0;
    void ** data = 0;
    if (a -> capacity <= a -> size) {
        data = a -> data;
        size = a -> size;
        int capacity = a -> capacity;
        if (SIZE_MAX / sizeof(void * ) < (size_t) capacity * 2 + 1) abort();
        void ** newData = malloc(((size_t) capacity * 2 + 1) * sizeof(void * ));
        if (newData == 0) abort();
        //@ assert malloc_block_pointers(newData, capacity * 2 + 1);
        //@ assert pointers_(newData, capacity * 2 + 1, _);
        memcpy(newData, data, (size_t) size * sizeof(void * ));
        //@ assert pointers(newData, size, vs);
        //@ assert pointers_(newData + size, (capacity * 2 + 1) - size, _);
        a -> data = newData;
        if (INT_MAX / 2 - 1 < capacity) abort();
        a -> capacity = capacity * 2 + 1;
        //@ assert a->capacity |-> (capacity * 2 + 1);
        free(data);
        //@ assert a->data |-> newData;
    }
    size = a -> size;
    data = a -> data;
    //@ assert data[0..size] |-> vs;
    //@ assert data[size..a->capacity] |-> _;
    data[size] = v;
    //@ assert data[size] |-> v;
    //@ pointers_split(data, size);
    //@ pointers_split(data + size, 1);
    //@ assert data[0..size] |-> vs;
    //@ assert data[size..size+1] |-> cons(v, nil);
    //@ assert data[size+1..a->capacity] |-> _;
    //@ pointers_join(data);
    //@ assert data[0..size+1] |-> append(vs, cons(v, nil));
    a -> size += 1;
    //@ assert a->size |-> (size + 1);
    //@ close arraylist(a, append(vs, cons(v, nil)));
}
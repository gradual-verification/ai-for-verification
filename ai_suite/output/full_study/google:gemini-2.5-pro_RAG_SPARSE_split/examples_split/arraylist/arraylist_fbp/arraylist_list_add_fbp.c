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
  0 <= size &*& size <= capacity &*&
  malloc_block_pointers(data, capacity) &*& data[0..size] |-> vs &*& data[size..capacity] |-> _;
@*/


// TODO: make this function pass the verification
void list_add(struct arraylist * a, void * v)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, append(vs, cons(v, nil)));
{
    //@ open arraylist(a, vs);
    if (a->capacity <= a->size) {
        //@ assert a->size |-> ?size &*& a->capacity |-> size;
        void **data = a->data;
        int capacity = a->capacity;
        
        if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
        int new_capacity = capacity * 2 + 1;
        if (INT_MAX / 2 - 1 < capacity) abort();
        
        void **newData = malloc((size_t)new_capacity * sizeof(void *));
        if (newData == 0) {
            //@ close arraylist(a, vs);
            abort();
        }
        
        //@ pointers_join(data);
        //@ pointers_to_chars(data);
        //@ size_t copy_size = (size_t)size * sizeof(void *);
        //@ chars__split(newData, copy_size);
        memcpy(newData, data, copy_size);
        //@ chars__join(newData);
        
        //@ chars_to_pointers(newData, size);
        //@ chars__to_pointers_(newData + size, new_capacity - size);
        
        a->data = newData;
        a->capacity = new_capacity;
        
        //@ pointers_to_chars(data);
        //@ chars_to_chars_(data);
        free(data);
    }
    
    //@ int current_size = a->size;
    //@ void **current_data = a->data;
    //@ pointers__split(current_data + current_size, 1);
    a->data[a->size] = v;
    a->size += 1;
    
    //@ pointers_join(current_data);
    //@ close arraylist(a, append(vs, cons(v, nil)));
}
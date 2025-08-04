#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

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


struct arraylist * create_arraylist()
//@ requires true;
//@ ensures arraylist(result, nil);
{
    struct arraylist * a = malloc(sizeof(struct arraylist));
    void * data = 0;
    if (a == 0) abort();
    a->size = 0;
    a->capacity = 100;
    data = malloc(100 * sizeof(void * ));
    if (data == 0) abort();
    a->data = data;
    //@ chars__to_pointers_(a->data, 100);
    //@ close arraylist(a, nil);
    return a;
}


void * list_get(struct arraylist * a, int i)
//@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
//@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
    //@ open arraylist(a, vs);
    void *res = a->data[i];
    //@ close arraylist(a, vs);
    return res;
}


void list_add(struct arraylist * a, void * v)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, append(vs, cons(v, nil)));
{
    //@ open arraylist(a, vs);
    if (a->capacity <= a->size) {
        void **old_data = a->data;
        int old_capacity = a->capacity;
        int size = a->size;
        
        if (SIZE_MAX / sizeof(void *) < (size_t)old_capacity * 2 + 1) abort();
        int new_capacity = old_capacity * 2 + 1;
        void **new_data = malloc((size_t)new_capacity * sizeof(void *));
        if (new_data == 0) abort();
        
        //@ pointers_to_chars(old_data);
        memcpy(new_data, old_data, (size_t)size * sizeof(void *));
        
        a->data = new_data;
        if (INT_MAX / 2 - 1 < old_capacity) abort();
        a->capacity = new_capacity;
        
        //@ pointers__to_chars_(old_data + size);
        //@ chars_chars__join(old_data);
        free(old_data);
        
        //@ chars_to_pointers(new_data, size);
        //@ chars__to_pointers_(new_data + size, new_capacity - size);
    }
    
    void **data = a->data;
    int size = a->size;
    int capacity = a->capacity;
    
    //@ pointers_split(data, size);
    //@ open pointers_(data + size, capacity - size, _);
    data[size] = v;
    a->size = size + 1;
    //@ close pointer(data + size, v);
    //@ pointers_join(data);
    //@ close arraylist(a, append(vs, cons(v, nil)));
}



void list_dispose(struct arraylist * a)
//@ requires arraylist(a, ?vs);
//@ ensures true;
{
    //@ open arraylist(a, vs);
    void ** data = a->data;
    int size = a->size;
    int capacity = a->capacity;
    
    //@ pointers_to_pointers_(data);
    //@ pointers__join(data);
    //@ pointers__to_chars_(data);
    
    free(data);
    free(a);
}


// TODO: make this function pass the verification
int main()
//@ requires true;
//@ ensures true;
{
    struct arraylist * a = create_arraylist();
    void * tmp = 0;
    list_add(a, (void * ) 10);
    list_add(a, (void * ) 20);

    tmp = list_get(a, 1);
    assert(tmp == (void * ) 20);
    list_dispose(a);

    return 0;
}
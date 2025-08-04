#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*&
  malloc_block_arraylist(a) &*&
  0 <= size &*& size <= capacity &*&
  data[0..size] |-> vs &*& data[size..capacity] |-> _ &*&
  malloc_block_pointers(data, capacity);
@*/


// TODO: make this function pass the verification
void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, append(vs, cons(v, nil)));
{
  //@ open arraylist(a, vs);
  //@ assert a->data |-> ?data_pre &*& a->size |-> ?size_pre &*& a->capacity |-> ?capacity_pre;
  //@ assert malloc_block_arraylist(a);
  //@ assert data_pre[0..size_pre] |-> vs &*& data_pre[size_pre..capacity_pre] |-> _;
  //@ assert malloc_block_pointers(data_pre, capacity_pre);

  int size = 0;
  void** data = 0;
  if(a->capacity <= a->size) {
    //@ assert size_pre == capacity_pre;
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ chars__to_pointers_(newData, capacity * 2 + 1);

    //@ pointers_to_chars(data, size);
    //@ pointers__split(newData, size);
    //@ pointers__to_chars_(newData, size);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ chars_to_pointers(newData, size);
    
    a->data = newData;
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    
    //@ pointers_to_chars(data, size);
    //@ chars_to_chars_(data, size * sizeof(void*));
    free(data);
  }
  
  //@ assert a->data |-> ?data_post &*& a->size |-> ?size_post &*& a->capacity |-> ?capacity_post;
  //@ assert data_post[0..size_post] |-> vs &*& data_post[size_post..capacity_post] |-> _;
  //@ assert malloc_block_pointers(data_post, capacity_post);
  //@ assert size_post == size_pre;
  //@ assert size_post < capacity_post;

  size = a->size;
  data = a->data;
  
  //@ pointers__split(data + size, 1);
  data[size] = v;
  a->size += 1;
  
  //@ pointers_join(data);
  
  //@ close arraylist(a, append(vs, cons(v, nil)));
}
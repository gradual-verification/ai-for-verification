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
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity  &*&
  data[0..size] |-> vs &*& data[size..capacity] |-> _;
@*/


// TODO: make this function pass the verification
void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, append(vs, cons(v, nil)));
{
  int size = 0;
  void** data = 0;
  if(a->capacity <= a->size) {
    //@ open arraylist(a, vs);
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ assert data[0..size] |-> vs;
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ assert newData[0..size] |-> vs;
    a->data = newData;
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    //@ assert newData[size..capacity * 2 + 1] |-> _;
    free(data);
    //@ close arraylist(a, vs);
  }
  //@ open arraylist(a, vs);
  size = a->size;
  data = a->data;
  data[size] = v;
  a->size += 1;
  //@ assert data[0..size] |-> vs;
  //@ assert data[size] |-> v;
  //@ assert data[size+1..a->capacity] |-> _;
  //@ close arraylist(a, append(vs, cons(v, nil)));
}
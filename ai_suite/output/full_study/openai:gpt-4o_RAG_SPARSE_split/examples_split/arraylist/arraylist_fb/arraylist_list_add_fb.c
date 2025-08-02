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
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ open pointers(data, size, vs);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ close pointers(newData, size, vs);
    a->data = newData;
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    //@ open pointers(data, size, vs);
    free(data);
  }
  size = a->size;
  data = a->data;
  //@ open pointers(data, size, vs);
  data[size] = v;
  //@ close pointers(data, size + 1, append(vs, cons(v, nil)));
  a->size += 1;
  //@ close arraylist(a, append(vs, cons(v, nil)));
}
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
  malloc_block_arraylist(a) &*&
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*&
  0 <= size &*& size <= capacity &*&
  malloc_block_pointers(data, capacity) &*&
  pointers(data, size, vs) &*&
  pointers_(data + size, capacity - size, _);
@*/


// TODO: make this function pass the verification
void list_dispose(struct arraylist* a)
//@ requires arraylist(a, ?vs);
//@ ensures true;
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  free(data);
  free(a);
}
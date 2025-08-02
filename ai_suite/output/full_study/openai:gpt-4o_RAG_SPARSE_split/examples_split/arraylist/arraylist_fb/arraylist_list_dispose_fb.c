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
  data[0..size] |-> vs &*& data[size..capacity] |-> _ &*& malloc_block(data, capacity * sizeof(void*)) &*& malloc_block(a, sizeof(struct arraylist));
@*/

// TODO: make this function pass the verification
void list_dispose(struct arraylist* a)
  //@ requires arraylist(a, ?vs);
  //@ ensures true;
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ open arraylist(a, vs);
  free(data);
  free(a);
}
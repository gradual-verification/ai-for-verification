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
void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?vs) &*& n >= 0 &*& n < length(vs);
//@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
  void** data = a->data;
  int size = a->size;
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
}


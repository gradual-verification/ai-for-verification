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
void *list_get(struct arraylist *a, int i)
  //@ requires arraylist(a, ?vs) &*& i >= 0 &*& i < length(vs);
  //@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
  //@ open arraylist(a, vs);
  void *result = a->data[i];
  //@ close arraylist(a, vs);
  return result;
}
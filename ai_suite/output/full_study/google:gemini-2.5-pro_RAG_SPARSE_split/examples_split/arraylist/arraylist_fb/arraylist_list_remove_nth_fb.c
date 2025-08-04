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
  //@ open arraylist(a, vs);
  //@ assert a->data |-> ?data_ptr &*& a->size |-> ?size &*& a->capacity |-> ?capacity;
  //@ assert data_ptr[0..size] |-> vs &*& data_ptr[size..capacity] |-> _;

  void** data = a->data;
  int size = a->size;

  //@ pointers_split(data, n);
  //@ pointers_split(data + n, 1);

  //@ list<void*> suffix = tail(drop(n, vs));
  //@ pointers_to_chars(data + n + 1);
  //@ assert chars(data + n + 1, (size - n - 1) * sizeof(void*), ?cs_src);
  //@ assert pointers_of_chars(cs_src) == suffix;

  //@ pointer_to_chars(data + n);

  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));

  //@ chars_to_pointers(data + n, size - n - 1);
  //@ pointers_join(data);

  //@ chars_to_chars_(data + size - 1);
  //@ chars__to_pointers_(data + size - 1, 1);
  //@ pointers__join(data + size - 1);

  a->size = a->size - 1;

  //@ close arraylist(a, append(take(n, vs), tail(drop(n, vs))));
}
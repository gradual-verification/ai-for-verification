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


void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?vs) &*& n >= 0 &*& n < length(vs);
//@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
  void** data = a->data;
  int size = a->size;
  
  //@ open arraylist(a, vs);
  //@ assert data[0..size] |-> vs;
  //@ pointers_split(data, n);
  //@ assert data[0..n] |-> ?vs1;
  //@ assert data[n..size] |-> ?vs2;
  //@ assert vs == append(vs1, vs2);
  //@ assert length(vs1) == n;
  //@ pointers_split(data + n, 1);
  //@ assert data[n..n+1] |-> ?vs_n;
  //@ assert data[n+1..size] |-> ?vs_rest;
  //@ assert vs2 == append(vs_n, vs_rest);
  //@ assert length(vs_n) == 1;
  //@ assert vs_n == cons(nth(n, vs), nil);
  
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  
  //@ assert data[n..size-1] |-> vs_rest;
  //@ pointers_join(data);
  //@ assert data[0..size-1] |-> append(vs1, vs_rest);
  //@ assert drop(n, vs) == append(vs_n, vs_rest);
  //@ assert tail(drop(n, vs)) == vs_rest;
  //@ assert append(vs1, vs_rest) == append(take(n, vs), tail(drop(n, vs)));
  
  a->size = a->size - 1;
  
  //@ close arraylist(a, append(take(n, vs), tail(drop(n, vs))));
}
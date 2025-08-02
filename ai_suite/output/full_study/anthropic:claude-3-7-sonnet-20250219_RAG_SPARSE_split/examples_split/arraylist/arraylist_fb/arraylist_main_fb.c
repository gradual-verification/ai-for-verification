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


struct arraylist *create_arraylist() 
  //@ requires true;
  //@ ensures arraylist(result, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  return a; 
}


void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?vs) &*& i >= 0 &*& i < length(vs);
//@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
  return a->data[i];
}


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
    memcpy(newData, data, (size_t)size * sizeof(void*));
    a->data = newData;
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    free(data);
  }
  size = a->size;
  data = a->data;
  data[size] = v;
  a->size += 1;
}


void list_dispose(struct arraylist* a)
//@ requires arraylist(a, ?vs);
//@ ensures true;
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  free(data);
  free(a);
}


// TODO: make this function pass the verification
int main()
//@ requires true;
//@ ensures true;
{
  struct arraylist* a = create_arraylist();
  void* tmp = 0;
  
  //@ open arraylist(a, nil);
  //@ assert a->size |-> 0;
  //@ assert a->data |-> ?data;
  //@ assert a->capacity |-> ?capacity;
  //@ assert data[0..0] |-> nil;
  //@ close arraylist(a, nil);
  
  list_add(a, (void *)10);
  
  //@ open arraylist(a, ?vs1);
  //@ assert a->size |-> 1;
  //@ assert a->data |-> ?data1;
  //@ assert data1[0..1] |-> ?elements1;
  //@ assert elements1 == cons((void*)10, nil);
  //@ close arraylist(a, vs1);
  
  list_add(a, (void *)20);
  
  //@ open arraylist(a, ?vs2);
  //@ assert a->size |-> 2;
  //@ assert a->data |-> ?data2;
  //@ assert data2[0..2] |-> ?elements2;
  //@ assert elements2 == append(vs1, cons((void*)20, nil));
  //@ close arraylist(a, vs2);
  
  tmp = list_get(a, 1);
  assert(tmp == (void*) 20);
  list_dispose(a);

  return 0;
}
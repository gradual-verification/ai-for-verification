#include <stdint.h>
#include <stdlib.h>
#include <string.h>
// #include "arraylist.h"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*&
  0 <= size &*& size <= capacity &*&
  data[0..size] 
  |-> vs &*& data[size..capacity] |-> _ &*&
  malloc_block_arraylist(a) &*& malloc_block_pointers(data, capacity);
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
  //@ close arraylist(a, nil);
  return a; 
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
//@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
  //@ open arraylist(a, vs);
  void *result = a->data[i];
  //@ close arraylist(a, vs);
  return result;
}

int list_length(struct arraylist *a)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, vs) &*& result == length(vs);
{
  //@ open arraylist(a, vs);
  int size = a->size;
  //@ close arraylist(a, vs);
  return size;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, append(vs, cons(v, nil)));
{
  int size = 0;
  void** data = 0;
  //@ open arraylist(a, vs);
  if(a->capacity <= a->size) {
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    //@ mul_mono_l(0, sizeof(void *), capacity * 2 + 1);
    //@ div_rem_nonneg(SIZE_MAX, sizeof(void *));
    //@ mul_mono_l(capacity * 2 + 1, SIZE_MAX / sizeof(void *), sizeof(void *));
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ mul_mono_l(0, size, sizeof(void *));
    //@ pointers__split(newData, size);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ chars_to_pointers(newData, size);
    a->data = newData;
    //@ div_rem_nonneg(INT_MAX, 2);
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    //@ chars_to_pointers(data, size);
    free(data);
  }
  size = a->size;
  data = a->data;
  data[size] = v;
  a->size += 1;
  //@ close pointers(data + size, 1, _);
  //@ close arraylist(a, append(vs, cons(v, nil)));
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?vs) &*& n >= 0 &*& n < length(vs);
//@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  int size = a->size;
  //@ pointers_limits(data);
  //@ mul_mono_l(0, n, sizeof(void *));
  //@ mul_mono_l(n + 1, length(vs), sizeof(void *));
  //@ pointers_split(data, n);
  //@ open pointers(data + n, _, _);
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
  //@ chars_to_pointers(data + n, size - n - 1);
  //@ chars_to_pointers(data + size - 1, 1);
  //@ close arraylist(a, append(take(n, vs), tail(drop(n, vs))));
}

void list_dispose(struct arraylist* a)
//@ requires arraylist(a, ?vs);
//@ ensures true;
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  free(data);
  free(a);
}

int main()
//@ requires true;
//@ ensures true;
{
  struct arraylist* a = create_arraylist();
  void* tmp = 0;
  list_add(a, (void *)10);
  list_add(a, (void *)20);
  
  tmp = list_get(a, 1);
  assert(tmp == (void*) 20);
  list_dispose(a);

  return 0;
}

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
  malloc_block_pointers(data, capacity) &*&
  pointers(data, size, vs) &*& pointers_(data + size, capacity - size, _) &*&
  length(vs) == size &*&
  0 <= size &*& size <= capacity;
@*/


struct arraylist *create_arraylist() 
  //@ requires true;
  //@ ensures arraylist(result, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  if(a == 0) abort();
  a->size = 0;
  void **data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  //@ chars__to_pointers_(data, 100);
  a->data = data;
  a->capacity = 100;
  //@ close arraylist(a, nil);
  return a; 
}


void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?vs) &*& i >= 0 &*& i < length(vs);
//@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
  //@ open arraylist(a, vs);
  void *res = a->data[i];
  //@ close arraylist(a, vs);
  return res;
}


void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, append(vs, cons(v, nil)));
{
  //@ open arraylist(a, vs);
  int size = a->size;
  int capacity = a->capacity;
  void** data = a->data;
  if(capacity <= size) {
    int new_capacity = capacity * 2 + 1;
    if (SIZE_MAX / sizeof(void *) < (size_t)new_capacity) abort();
    void** newData = malloc((size_t)new_capacity * sizeof(void*));
    if(newData == 0) abort();
    //@ chars__to_pointers_(newData, new_capacity);
    
    //@ pointers_to_chars(data);
    //@ pointers__split(newData, size);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ chars_to_pointers(newData, size);
    
    a->data = newData;
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = new_capacity;
    
    //@ chars_to_chars_(data);
    free(data);
    
    data = newData;
  }
  
  size = a->size;
  data = a->data;
  
  //@ pointers__split(data + size, 1);
  data[size] = v;
  a->size += 1;
  
  //@ pointers_join(data);
  //@ close arraylist(a, append(vs, cons(v, nil)));
}


void list_dispose(struct arraylist* a)
//@ requires arraylist(a, ?vs);
//@ ensures true;
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  //@ pointers_pointers__join(data);
  //@ pointers__to_chars_(data);
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
  list_add(a, (void *)10);
  list_add(a, (void *)20);
  
  tmp = list_get(a, 1);
  assert(tmp == (void*) 20);
  list_dispose(a);

  return 0;
}
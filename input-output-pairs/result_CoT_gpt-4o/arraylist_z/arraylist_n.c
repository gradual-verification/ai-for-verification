#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

// Predicate for arraylist structure
// Defines the conditions for a valid arraylist
predicate valid_arraylist(struct arraylist* a, void** data, int size, int capacity) =
  a->data |-> data &*& a->size |-> size &*& a->capacity |-> capacity &*&
  data != 0 &*& malloc_block(data, capacity * sizeof(void*)) &*&
  0 <= size &*& size <= capacity &*&
  malloc_block(a, sizeof(struct arraylist));

// Create a new array list
struct arraylist *create_arraylist()
  //@ requires true;
  //@ ensures valid_arraylist(result, ?data, 0, 100) &*& result != 0;
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  //@ close valid_arraylist(a, data, 0, 100);
  return a; 
}

// Get the element at index i
void *list_get(struct arraylist *a, int i)
  //@ requires valid_arraylist(a, ?data, ?size, ?capacity) &*& 0 <= i &*& i < size;
  //@ ensures valid_arraylist(a, data, size, capacity) &*& result == data[i];
{
  //@ open valid_arraylist(a, data, size, capacity);
  return a->data[i];
  //@ close valid_arraylist(a, data, size, capacity);
}

// Get the size of the list
int list_length(struct arraylist *a)
  //@ requires valid_arraylist(a, ?data, ?size, ?capacity);
  //@ ensures valid_arraylist(a, data, size, capacity) &*& result == size;
{
  //@ open valid_arraylist(a, data, size, capacity);
  return a->size;
  //@ close valid_arraylist(a, data, size, capacity);
}

// Add an element to the list
void list_add(struct arraylist *a, void *v)
  //@ requires valid_arraylist(a, ?data, ?size, ?capacity);
  //@ ensures valid_arraylist(a, ?nData, size + 1, ?newCapacity) &*& newCapacity >= size + 1;
{
  //@ open valid_arraylist(a, data, size, capacity);
  int size = 0;
  void** newData = 0;
  if(a->capacity <= a->size) {
    size = a->size;
    int capacity = a->capacity;
    if(SIZE_MAX / sizeof(void*) < (size_t)capacity * 2 + 1) abort();
    newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    memcpy(newData, data, (size_t)size * sizeof(void*));
    a->data = newData;
    if(INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    free(data);
  }
  size = a->size;
  data = a->data;
  data[size] = v;
  a->size += 1;
  //@ close valid_arraylist(a, a->data, a->size, a->capacity);
}

// Remove the nth element
void list_remove_nth(struct arraylist *a, int n)
  //@ requires valid_arraylist(a, ?data, ?size, ?capacity) &*& 0 <= n &*& n < size;
  //@ ensures valid_arraylist(a, data, size - 1, capacity);
{
  //@ open valid_arraylist(a, data, size, capacity);
  memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
  //@ close valid_arraylist(a, data, size - 1, capacity);
}

// Dispose the array list
void list_dispose(struct arraylist* a)
  //@ requires valid_arraylist(a, ?data, ?size, ?capacity);
  //@ ensures true;
{
  //@ open valid_arraylist(a, data, size, capacity);
  free(a->data);
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

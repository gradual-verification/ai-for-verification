#include <stdint.h>
#include <stdlib.h>
#include <string.h>

//@ #include "prelude.h"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void *> elements) =
  a->size |-> ?size &*& a->capacity |-> ?capacity &*&
  a->data |-> ?data &*&
  malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity) &*&
  0 <= size &*& size <= capacity &*&
  pointers(data, size, elements) &*&
  pointers(data + size, capacity - size, _);
@*/

/***
 * Description:
The create_arraylist function allocates memory for a new array list structure.

@param none

The function initializes an array list whose the data points to a newly allocated array and has no element.
*/
//@ requires true;
//@ ensures result != 0 &*& arraylist(result, nil);
struct arraylist *create_arraylist()  
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

/***
 * Description:
The list_get function gets the element of the arraylist whose index is i. 
It requires that i is within the range of the arraylist.

@param a - the arraylist to be accessed.
@param i - the index of the element to be returned.

The function ensures that the arraylist is not modified at the end, and the return value is the i-th of the arraylist.
*/
//@ requires arraylist(a, ?elements) &*& 0 <= i &*& i < length(elements);
//@ ensures arraylist(a, elements) &*& result == nth(i, elements);
void *list_get(struct arraylist *a, int i)
{
  //@ open arraylist(a, elements);
  return a->data[i];
  //@ close arraylist(a, elements);
}

/***
 * Description:
The list_add function adds a new element to the end of the dynamic array list (struct arraylist).

@param a - the arraylist to be added to.
@param v - the new element to be added into the arraylist.

It makes sure that a new element v is added to the end of the array list. 
*/
//@ requires arraylist(a, ?elements) &*& length(elements) < a->capacity;
//@ ensures arraylist(a, append(elements, {v}));
void list_add(struct arraylist *a, void *v)
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
  //@ close arraylist(a, append(elements, {v}));
}

/***
 * Description:
The list_dispose function deallocates the memory associated with a dynamic array list (struct arraylist).

@param a - the arraylist to be de-allocated

This function ensures that all dynamically allocated memory used by the array list is properly released to prevent memory leaks.
*/
//@ requires arraylist(a, _);
//@ ensures true;
void list_dispose(struct arraylist* a)
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ open arraylist(a, _);
  free(data);
  free(a);
}

// TODO: make this function pass the verification
/**
 * Description:
The main function tests the operation of an arraylist.
*/
//@ requires true;
//@ ensures true;
int main()
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
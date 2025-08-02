#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "prelude.h"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

//@ predicate arraylist(struct arraylist *a, int capacity, list<void *> values) =
//@   a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> capacity &*&
//@   0 <= size &*& size <= capacity &*& pointers(data, capacity, ?elems) &*&
//@   malloc_block_pointers(data, capacity) &*& values == take(size, elems);

/***
 * Description:
The list_add function adds a new element to the end of the dynamic array list (struct arraylist).

@param a - the arraylist to be added to.
@param v - the new element to be added into the arraylist.

It makes sure that a new element v is added to the end of the array list. 
*/
//@ requires arraylist(a, ?capacity, ?values);
//@ ensures arraylist(a, ?new_capacity, append(values, {v})) &*& new_capacity >= capacity;
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
    //@ pointers_split(data, size);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    a->data = newData;
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    free(data);
    //@ pointers_join(newData);
  }
  size = a->size;
  data = a->data;
  //@ pointers_split(data, size);
  data[size] = v;
  a->size += 1;
  //@ pointers_join(data);
}
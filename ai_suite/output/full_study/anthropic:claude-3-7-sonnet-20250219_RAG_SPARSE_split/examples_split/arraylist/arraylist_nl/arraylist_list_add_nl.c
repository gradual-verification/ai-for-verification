#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a, list<void *> elements) =
    a != 0 &*&
    a->data |-> ?data &*&
    a->size |-> ?size &*&
    a->capacity |-> ?capacity &*&
    malloc_block_arraylist(a) &*&
    0 <= size &*& size <= capacity &*&
    data != 0 &*&
    pointers(data, size, elements) &*&
    pointers_(data + size, capacity - size, _) &*&
    malloc_block_pointers(data, capacity);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_add function adds a new element to the end of the dynamic array list (struct arraylist).

@param a - the arraylist to be added to.
@param v - the new element to be added into the arraylist.

It makes sure that a new element v is added to the end of the array list. 
*/
void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?elements);
//@ ensures arraylist(a, append(elements, cons(v, nil)));
{
  int size = 0;
  void** data = 0;
  //@ open arraylist(a, elements);
  if(a->capacity <= a->size) {
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ close pointers(data, size, elements);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ open pointers(newData, size, elements);
    a->data = newData;
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    free(data);
    //@ close pointers(newData, size, elements);
  }
  size = a->size;
  data = a->data;
  //@ assert pointers(data, size, elements);
  //@ open pointers_(data + size, a->capacity - size, _);
  data[size] = v;
  //@ close pointers(data + size, 1, cons(v, nil));
  //@ pointers_join(data);
  a->size += 1;
  //@ close arraylist(a, append(elements, cons(v, nil)));
}
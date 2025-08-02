#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
  predicate arraylist(struct arraylist *a, int size, int capacity, list<void *> elements) =
    a != 0 &*&
    a->data |-> ?data &*&
    a->size |-> size &*&
    a->capacity |-> capacity &*&
    size >= 0 &*&
    size <= capacity &*&
    capacity > 0 &*&
    pointers(data, size, elements) &*&
    pointers_(data + size, capacity - size, _) &*&
    malloc_block_pointers(data, capacity) &*&
    malloc_block_arraylist(a);
@*/

/***
 * Description:
The create_arraylist function allocates memory for a new array list structure.

@param none

The function initializes an array list whose the data points to a newly allocated array and has no element.
*/
struct arraylist *create_arraylist()  
//@ requires true;
//@ ensures result != 0 &*& arraylist(result, 0, 100, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  //@ close pointers(data, 0, nil);
  //@ close pointers_(data + 0, 100 - 0, _);
  //@ close arraylist(a, 0, 100, nil);
  return a; 
}
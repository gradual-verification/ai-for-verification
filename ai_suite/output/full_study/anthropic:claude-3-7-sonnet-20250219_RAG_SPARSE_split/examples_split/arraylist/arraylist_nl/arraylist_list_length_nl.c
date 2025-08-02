#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
// Define a predicate for the arraylist structure
predicate arraylist(struct arraylist *a, list<void *> items) =
    a != 0 &*&
    a->data |-> ?data &*&
    a->size |-> ?size &*&
    a->capacity |-> ?capacity &*&
    malloc_block_arraylist(a) &*&
    data != 0 &*&
    pointers(data, size, items) &*&
    pointers_(data + size, capacity - size, _) &*&
    malloc_block_pointers(data, capacity) &*&
    0 <= size &*& size <= capacity;
@*/

/***
 * Description:
The list_length function gets the length (i.e., number of elements) of a non-null arraylist. 

@param a - the arraylist whose length is to be retrieved.
*/
int list_length(struct arraylist *a)
/*@ requires arraylist(a, ?items); @*/
/*@ ensures arraylist(a, items) &*& result == length(items); @*/
{
  //@ open arraylist(a, items);
  int result = a->size;
  //@ close arraylist(a, items);
  return result;
}
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

//@ #include "arrays.gh"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

//@ predicate arraylist(struct arraylist *a, int capacity, list<void *> elements) =
//@   a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> capacity &*&
//@   0 <= size &*& size <= capacity &*& malloc_block(data, capacity * sizeof(void *)) &*&
//@   pointers(data, size, elements) &*& pointers(data + size, capacity - size, _);

/***
 * Description:
The list_get function gets the element of the arraylist whose index is i. 
It requires that i is within the range of the arraylist.

@param a - the arraylist to be accessed.
@param i - the index of the element to be returned.

The function ensures that the arraylist is not modified at the end, and the return value is the i-th of the arraylist.
*/
// TODO: make this function pass the verification
void *list_get(struct arraylist *a, int i)
  //@ requires arraylist(a, ?capacity, ?elements) &*& 0 <= i &*& i < length(elements);
  //@ ensures arraylist(a, capacity, elements) &*& result == nth(i, elements);
{
  //@ open arraylist(a, capacity, elements);
  void *result = a->data[i];
  //@ close arraylist(a, capacity, elements);
  return result;
}
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

// TODO: make this function pass the verification
/***
 * Description:
The list_get function gets the element of the arraylist whose index is i. 
It requires that i is within the range of the arraylist.

@param a - the arraylist to be accessed.
@param i - the index of the element to be returned.

The function ensures that the arraylist is not modified at the end, and the return value is the i-th of the arraylist.
*/
void *list_get(struct arraylist *a, int i)
//@ requires a != 0 &*& a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*& i >= 0 &*& i < size &*& pointers(data, size, ?elements);
//@ ensures a != 0 &*& a->data |-> data &*& a->size |-> size &*& a->capacity |-> capacity &*& pointers(data, size, elements) &*& result == nth(i, elements);
{
  return a->data[i];
}
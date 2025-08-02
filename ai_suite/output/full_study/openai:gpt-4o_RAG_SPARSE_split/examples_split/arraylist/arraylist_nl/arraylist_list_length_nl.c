#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// Define the struct arraylist
struct arraylist {
  void **data;
  int size;
  int capacity;
};

// Predicate to describe the state of an arraylist
/*@
predicate arraylist(struct arraylist *a, int size, int capacity, list<void *> elements) =
  a->data |-> ?data &*&
  a->size |-> size &*&
  a->capacity |-> capacity &*&
  malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity) &*&
  0 <= size &*& size <= capacity &*&
  pointers(data, size, elements);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The list_length function gets the length (i.e., number of elements) of a non-null arraylist. 
 *
 * @param a - the arraylist whose length is to be retrieved.
 */
/*@
requires arraylist(a, ?size, ?capacity, ?elements);
ensures arraylist(a, size, capacity, elements) &*& result == size;
@*/
int list_length(struct arraylist *a)
{
  return a->size;
}
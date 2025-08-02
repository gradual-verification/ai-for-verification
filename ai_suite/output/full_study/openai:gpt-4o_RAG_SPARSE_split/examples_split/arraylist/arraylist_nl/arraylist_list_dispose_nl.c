#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// Define the struct arraylist
struct arraylist {
  void **data;
  int size;
  int capacity;
};

// Predicate for the arraylist
/*@
predicate arraylist(struct arraylist *a, int size, int capacity, list<void *> elements) =
  a->data |-> ?data &*&
  a->size |-> size &*&
  a->capacity |-> capacity &*&
  malloc_block_pointers(data, capacity) &*&
  pointers(data, size, elements) &*&
  malloc_block_arraylist(a);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_dispose function deallocates the memory associated with a dynamic array list (struct arraylist).

@param a - the arraylist to be de-allocated

This function ensures that all dynamically allocated memory used by the array list is properly released to prevent memory leaks.
*/
void list_dispose(struct arraylist* a)
  //@ requires arraylist(a, ?size, ?capacity, ?elements);
  //@ ensures emp;
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ open arraylist(a, size, capacity, elements);
  free(data);
  free(a);
}
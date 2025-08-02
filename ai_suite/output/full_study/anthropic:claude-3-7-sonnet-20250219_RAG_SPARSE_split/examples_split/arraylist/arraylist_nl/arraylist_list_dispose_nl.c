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
predicate arraylist(struct arraylist *a, list<void *> elements) =
    a != 0 &*&
    a->data |-> ?data &*&
    a->size |-> ?size &*&
    a->capacity |-> ?capacity &*&
    size >= 0 &*&
    capacity >= size &*&
    pointers(data, size, elements) &*&
    data[size..capacity] |-> _ &*&
    malloc_block_pointers(data, capacity) &*&
    malloc_block_arraylist(a);
@*/

/***
 * Description:
The list_dispose function deallocates the memory associated with a dynamic array list (struct arraylist).

@param a - the arraylist to be de-allocated

This function ensures that all dynamically allocated memory used by the array list is properly released to prevent memory leaks.
*/
void list_dispose(struct arraylist* a)
    //@ requires arraylist(a, ?elements);
    //@ ensures emp;
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ open arraylist(a, elements);
  free(data);
  free(a);
}
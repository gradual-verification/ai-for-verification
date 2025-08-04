#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> items) =
    a->data |-> ?data &*&
    a->size |-> ?size &*&
    a->capacity |-> ?capacity &*&
    malloc_block_arraylist(a) &*&
    0 <= size &*& size <= capacity &*&
    length(items) == size &*&
    pointers(data, size, items) &*&
    pointers_(data + size, capacity - size, _) &*&
    malloc_block_pointers(data, capacity);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The list_length function gets the length (i.e., number of elements) of a non-null arraylist. 

@param a - the arraylist whose length is to be retrieved.
*/
int list_length(struct arraylist *a)
/*@
requires [?f]arraylist(a, ?items);
ensures [f]arraylist(a, items) &*& result == length(items);
@*/
{
  return a->size;
}
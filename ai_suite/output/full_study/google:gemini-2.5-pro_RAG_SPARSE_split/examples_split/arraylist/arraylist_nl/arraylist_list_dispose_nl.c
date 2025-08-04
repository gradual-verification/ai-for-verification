#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist_pred(struct arraylist *a; list<void*> items) =
    a->data |-> ?data
    &*& a->size |-> ?size
    &*& a->capacity |-> ?capacity
    &*& malloc_block_arraylist(a)
    &*& size == length(items)
    &*& 0 <= size &*& size <= capacity
    &*& data == 0 ?
        capacity == 0
    :
        pointers(data, size, items) &*&
        pointers_(data + size, capacity - size, _) &*&
        malloc_block(data, (unsigned int)capacity * sizeof(void*));
@*/


// TODO: make this function pass the verification
/***
 * Description:
The list_dispose function deallocates the memory associated with a dynamic array list (struct arraylist).

@param a - the arraylist to be de-allocated

This function ensures that all dynamically allocated memory used by the array list is properly released to prevent memory leaks.
*/
void list_dispose(struct arraylist* a)
    //@ requires arraylist_pred(a, ?items);
    //@ ensures emp;
{
  //@ open arraylist_pred(a, items);
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  
  //@ if (data == 0) {
  //@     close chars_(data, 0, nil);
  //@ } else {
  //@     pointers_pointers__join(data);
  //@     pointers__to_chars_(data);
  //@ }
  free(data);
  free(a);
}
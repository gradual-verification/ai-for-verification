#include <stdint.h>
#include <stdlib.h>
#include <string.h>

//@ #include "prelude.h"
//@ #include "list.gh"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

//@ predicate arraylist(struct arraylist *a, list<void *> elements) =
//@   a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*&
    0 <= size &*& size <= capacity &*&
    pointers(data, capacity, ?elems) &*&
    elements == take(size, elems);

// TODO: make this function pass the verification
/*** 
 * Description:
The list_remove_nth function removes the element at the specified index n from the dynamic array list (struct arraylist). 

@param a - the non-empty arraylist whose element will be removed.
@param n - the index of the element to be removed in the original arraylist, should be within the range of arraylist.

It ensures that the arraylist has the original n-th element removed, with the elements after it shifted left by one position.
*/
//@ requires arraylist(a, ?elements) &*& 0 <= n &*& n < length(elements);
//@ ensures arraylist(a, remove_nth(n, elements));
void list_remove_nth(struct arraylist *a, int n)
{
  void** data = a->data;
  int size = a->size;
  //@ pointers_split(data, n);
  //@ pointers_split(data + n + 1, size - n - 1);
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
  //@ pointers_join(data);
  //@ pointers_join(data);
}
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> elements) =
  a != 0 &*&
  a->data |-> ?data &*&
  a->size |-> ?size &*&
  a->capacity |-> ?capacity &*&
  malloc_block_arraylist(a) &*&
  data != 0 &*&
  malloc_block_pointers(data, capacity) &*&
  pointers(data, size, elements) &*&
  pointers_(data + size, capacity - size, _) &*&
  0 <= size &*& size <= capacity;
@*/

// TODO: make this function pass the verification
/*** 
 * Description:
The list_remove_nth function removes the element at the specified index n from the dynamic array list (struct arraylist). 

@param a - the non-empty arraylist whose element will be removed.
@param n - the index of the element to be removed in the original arraylist, should be within the range of arraylist.

It ensures that the arraylist has the original n-th element removed, with the elements after it shifted left by one position.
*/
void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?elements) &*& 0 <= n &*& n < length(elements);
//@ ensures arraylist(a, remove_nth(n, elements));
{
  //@ open arraylist(a, elements);
  void** data = a->data;
  int size = a->size;
  
  //@ assert pointers(data, size, elements);
  //@ pointers_split(data, n);
  //@ assert pointers(data, n, take(n, elements));
  //@ assert pointers(data + n, size - n, drop(n, elements));
  //@ pointers_split(data + n, 1);
  //@ assert pointers(data + n, 1, take(1, drop(n, elements)));
  //@ assert pointers(data + n + 1, size - n - 1, drop(1, drop(n, elements)));
  
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  
  //@ assert pointers(data + n, size - n - 1, drop(1, drop(n, elements)));
  //@ pointers_join(data);
  //@ assert pointers(data, n + (size - n - 1), append(take(n, elements), drop(1, drop(n, elements))));
  //@ drop_take_remove_nth(elements, n);
  //@ assert append(take(n, elements), tail(drop(n, elements))) == remove_nth(n, elements);
  //@ assert pointers(data, size - 1, remove_nth(n, elements));
  
  a->size = a->size - 1;
  
  //@ close arraylist(a, remove_nth(n, elements));
}
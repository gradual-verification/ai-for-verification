#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
    a->data |-> ?data
    &*& a->size |-> ?size
    &*& a->capacity |-> ?capacity
    &*& malloc_block(a, sizeof(struct arraylist))
    &*& size == length(vs)
    &*& 0 <= size &*& size <= capacity
    &*& data[0..size] |-> vs
    &*& data[size..capacity] |-> _
    &*& malloc_block_pointers(data, capacity);
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
/*@
requires arraylist(a, ?vs) &*& 0 <= n &*& n < length(vs);
ensures arraylist(a, remove_nth(n, vs));
@*/
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  int size = a->size;
  
  // Split the array to isolate the regions for memmove.
  //@ pointers_split(data, n);
  //@ pointers_split(data + n, 1);
  
  // Convert pointer arrays to char arrays for memmove.
  // pointers_to_chars also produces a has_type fact, needed for the conversion back.
  //@ pointers_to_chars(data + n + 1);
  //@ pointers_to_chars(data + n);
  
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  
  // Convert the moved region back to a pointer array.
  // This consumes the has_type(data + n, ...) fact.
  //@ chars_to_pointers(data + n, size - n - 1);
  
  // Join the prefix with the moved region.
  //@ pointers_join(data);
  
  // Prove that the logical list of pointers is correct.
  //@ drop_take_remove_nth(vs, n);
  
  a->size = a->size - 1;
  
  // Reconstruct the chunk for the unused part of the array.
  // The last element is now unused. memmove gives us a `chars` chunk for it.
  // We convert it to `pointers_` and join it with the rest of the unused capacity.
  //@ chars_to_chars_(data + size - 1);
  //@ has_type_ptr_add_((pointer)(data + n), (size - 1) - n, &typeid(void*));
  //@ chars__to_pointers_(data + size - 1, 1);
  //@ pointers__join(data + size - 1);
  
  //@ close arraylist(a, remove_nth(n, vs));
}
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
The list_remove_nth function removes the element at the specified index n from the dynamic array list (struct arraylist). 

@param a - the non-empty arraylist whose element will be removed.
@param n - the index of the element to be removed in the original arraylist, should be within the range of arraylist.

It ensures that the arraylist has the original n-th element removed, with the elements after it shifted left by one position.
*/
void list_remove_nth(struct arraylist *a, int n)
{
  void** data = a->data;
  int size = a->size;
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
}


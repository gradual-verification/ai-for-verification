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
The list_dispose function deallocates the memory associated with a dynamic array list (struct arraylist).

@param a - the arraylist to be de-allocated

This function ensures that all dynamically allocated memory used by the array list is properly released to prevent memory leaks.
*/
void list_dispose(struct arraylist* a)
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  free(data);
  free(a);
}


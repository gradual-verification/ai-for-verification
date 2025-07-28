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
The list_length function gets the length (i.e., number of elements) of a non-null arraylist. 

@param a - the arraylist whose length is to be retrieved.
*/
int list_length(struct arraylist *a)
{
  return a->size;
}


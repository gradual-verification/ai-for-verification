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
The create_arraylist function allocates memory for a new array list structure.

@param none

The function initializes an array list whose the data points to a newly allocated array and has no element.
*/
struct arraylist *create_arraylist()  
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  return a; 
}


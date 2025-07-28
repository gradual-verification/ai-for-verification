#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};


// TODO: make this function pass the verification
/***
 * Description:
The `create_person` function allocates and initializes a new `person` struct with no spouse.

It makes sure that the return value is a non-null person with its spouse as null. 
*/
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  return p;
}


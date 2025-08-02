#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person* p; char* name, struct person* spouse) =
    p != 0 &*&
    p->name |-> name &*&
    p->spouse |-> spouse;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `create_person` function allocates and initializes a new `person` struct with no spouse.

It makes sure that the return value is a non-null person with its spouse as null. 
*/
/*@
requires emp;
ensures result != 0 &*& person(result, _, 0);
@*/
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  //@ close person(p, _, 0);
  return p;
}
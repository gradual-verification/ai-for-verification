#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@

// A predicate representing a person object.
// The `name` field is represented by an `option` type.
// `none` means the `name` pointer is uninitialized.
// `some(n)` means the `name` pointer is initialized to `n`.
// The `spouse` pointer is always initialized.
predicate person(struct person *p; option<char *> name, struct person *spouse) =
    malloc_block_person(p) &*&
    (name == none ? p->name |-> _ : p->name |-> the(name)) &*&
    p->spouse |-> spouse;

@*/


// TODO: make this function pass the verification
/***
 * Description:
The `create_person` function allocates and initializes a new `person` struct with no spouse.

It makes sure that the return value is a non-null person with its spouse as null. 
*/
/*@
requires true;
ensures person(result, none, 0);
@*/
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  return p;
}
#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p; char *name, struct person *spouse) =
    p->name |-> name &*&
    p->spouse |-> spouse;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `person_get_spouse` function retrieves the spouse of the given `person`.

@param `this` - Pointer to the `person` whose spouse is to be retrieved

It makes sure that `this` person is not changed and its spouse is returned.
*/
struct person* person_get_spouse(struct person* this)
    //@ requires person(this, ?n, ?s);
    //@ ensures person(this, n, s) &*& result == s;
{
  return this->spouse;
}
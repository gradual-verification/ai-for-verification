#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

//@ predicate person(struct person* p; struct person* spouse) = p->spouse |-> spouse;

// TODO: make this function pass the verification
/***
 * Description:
The `person_get_spouse` function retrieves the spouse of the given `person`.

@param `this` - Pointer to the `person` whose spouse is to be retrieved

It makes sure that `this` person is not changed and its spouse is returned.
*/
//@ requires person(this, ?spouse);
//@ ensures person(this, spouse) &*& result == spouse;
struct person* person_get_spouse(struct person* this)
{
  return this->spouse;
}
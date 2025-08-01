#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};


// TODO: make this function pass the verification
/***
 * Description:
The `marry` function marries two unmarried `person` instances by setting their spouse pointers to each other.

@param `this` - Pointer to the first `person` whose spouse is null
@param `other` - Pointer to the second `person` whose spouse is null

It makes sure that this and other are married to each other. 
*/
void marry(struct person *this, struct person *other)
{
  this->spouse = other;
  other->spouse = this;
}


#include "stdlib.h"

/*@
// A predicate to represent ownership of a person struct and its fields.
predicate person_info(struct person *p; char* name, struct person* spouse) =
    p->name |-> name &*&
    p->spouse |-> spouse &*&
    malloc_block_person(p);
@*/

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
    //@ requires person_info(this, ?n1, 0) &*& person_info(other, ?n2, 0) &*& this != other;
    //@ ensures person_info(this, n1, other) &*& person_info(other, n2, this);
{
  this->spouse = other;
  other->spouse = this;
}
#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

//@ predicate person(struct person* p; struct person* spouse) = p->spouse |-> spouse;

/*@
predicate_family_instance person_divorce_pre(void *divorce)(struct person *this) =
    person(this, ?spouse) &*& spouse != 0 &*& person(spouse, this);

predicate_family_instance person_divorce_post(void *divorce)(struct person *this) =
    person(this, 0) &*& person(?spouse, 0);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `divorce` function divorces two married `person` instances by setting their spouse pointers to `0`.

@param `this` - Pointer to one `person` in the marriage

It makes sure that `this` person and its original spouse has their spouses as null. 
*/
//@ requires person_divorce_pre(divorce)(this);
//@ ensures person_divorce_post(divorce)(this);
void divorce(struct person* this)
{
  this->spouse->spouse = 0;
  this->spouse = 0;
}
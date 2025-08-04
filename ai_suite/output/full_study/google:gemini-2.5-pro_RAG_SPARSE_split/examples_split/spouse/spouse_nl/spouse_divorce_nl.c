#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
// A person struct is valid if it's not null, its fields point to valid values,
// and it corresponds to an allocated memory block.
predicate person(struct person *p; char* name, struct person* spouse) =
    p != 0 &*&
    p->name |-> name &*&
    p->spouse |-> spouse &*&
    malloc_block_person(p);

// Two persons, p1 and p2, are married if they are distinct and are each other's spouse.
// This predicate consumes the individual 'person' predicates for both.
predicate married(struct person *p1, struct person *p2) =
    p1 != p2 &*&
    person(p1, ?n1, p2) &*&
    person(p2, ?n2, p1);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The `divorce` function divorces two married `person` instances by setting their spouse pointers to `0`.

@param `this` - Pointer to one `person` in the marriage

It makes sure that `this` person and its original spouse has their spouses as null. 
*/
void divorce(struct person* this)
    //@ requires married(this, ?s);
    //@ ensures person(this, ?n1, 0) &*& person(s, ?n2, 0);
{
  //@ open married(this, s);
  this->spouse->spouse = 0;
  this->spouse = 0;
}
#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
// A person is a valid memory block.
// If the person is single (spouse == 0), we have full ownership of the spouse field.
// If the person is married (spouse != 0), the ownership of the spouse fields
// is split between the two person predicates. Each predicate holds half the permission
// for both `p->spouse` and `spouse->spouse`.
predicate person(struct person *p, struct person *spouse) =
  p != 0 &*& p->name |-> _ &*& malloc_block_person(p) &*&
  (
    spouse == 0 ?
      p->spouse |-> 0
    :
      p != spouse &*&
      [1/2]p->spouse |-> spouse &*& [1/2]spouse->spouse |-> p
  );
@*/


// TODO: make this function pass the verification
void marry(struct person *this, struct person *other)
//@ requires person(this, 0) &*& person(other, 0);
//@ ensures person(this, other) &*& person(other, this);
{
  //@ open person(this, 0);
  //@ open person(other, 0);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, other);
  //@ close person(other, this);
}
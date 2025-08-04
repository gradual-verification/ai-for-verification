// person(p, 0) expands to:
p->name |-> _ &*& p->spouse |-> 0
// person(p, s) where s != 0 expands to:
p->name |-> _ &*& p != s &*& [1/2]p->spouse |-> s &*& [1/2]s->spouse |-> p
#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p, struct person *spouse) =
  p->name |-> _ &*& (spouse == 0 ? p->spouse |-> 0 : p!=spouse 
  &*& [1/2] p->spouse |-> spouse &*& [1/2] spouse->spouse |-> p);
@*/


// TODO: make this function pass the verification
void marry(struct person *this, struct person *other)
//@ requires person(this, 0) &*& person(other, 0);
//@ ensures person(this, other) &*& person(other, this);
{
  this->spouse = other;
  other->spouse = this;
}
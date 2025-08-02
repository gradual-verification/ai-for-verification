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
  //@ open person(this, 0);
  //@ open person(other, 0);
  
  this->spouse = other;
  other->spouse = this;
  
  //@ close [1/2]this->spouse |-> other;
  //@ close [1/2]other->spouse |-> this;
  //@ close person(this, other);
  //@ close person(other, this);
}
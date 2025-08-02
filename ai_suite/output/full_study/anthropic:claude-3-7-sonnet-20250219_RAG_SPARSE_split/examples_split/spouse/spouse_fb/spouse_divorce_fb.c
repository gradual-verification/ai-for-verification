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

void divorce(struct person* this)
//@ requires person(this, ?other) &*& person(other, this);
//@ ensures person(this, 0) &*& person(other, 0);
{
  //@ open person(this, other);
  //@ open person(other, this);
  
  // At this point we have:
  // [1/2]this->spouse |-> other
  // [1/2]other->spouse |-> this
  // [1/2]this->spouse |-> other (from opening person(other, this))
  // [1/2]other->spouse |-> this (from opening person(this, other))
  
  // Now we have full permission to both spouse fields
  
  this->spouse->spouse = 0;
  this->spouse = 0;
  
  //@ close person(other, 0);
  //@ close person(this, 0);
}
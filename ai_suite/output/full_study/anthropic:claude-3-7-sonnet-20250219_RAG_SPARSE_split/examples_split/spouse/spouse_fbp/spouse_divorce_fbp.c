#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p, struct person *spouse) =
  p != 0 &*& p->name |-> _ &*& (spouse == 0 ? p->spouse |-> 0 : p!=spouse 
  &*& [1/2] p->spouse |-> spouse &*& [1/2] spouse->spouse |-> p) &*&  malloc_block_person(p);
@*/

void divorce(struct person* this)
//@ requires person(this, ?other) &*& person(other, this);
//@ ensures person(this, 0) &*& person(other, 0);
{
  //@ open person(this, other);
  //@ open person(other, this);
  
  //@ assert [1/2]this->spouse |-> other;
  //@ assert [1/2]other->spouse |-> this;
  
  this->spouse->spouse = 0;
  this->spouse = 0;
  
  //@ close person(other, 0);
  //@ close person(this, 0);
}
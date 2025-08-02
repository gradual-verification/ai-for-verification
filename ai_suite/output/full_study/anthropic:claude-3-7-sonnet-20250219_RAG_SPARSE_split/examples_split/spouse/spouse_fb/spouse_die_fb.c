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


void die(struct person *this)
//@ requires person(this, ?other) &*& (other == 0 ? true : person(other, this));
//@ ensures other == 0 ? true : person(other, 0);
{
  //@ open person(this, other);
  if(this->spouse != 0) {
    //@ assert [1/2]this->spouse |-> ?spouse;
    //@ assert spouse == other;
    //@ assert this != spouse;
    //@ assert [1/2]spouse->spouse |-> this;
    //@ open person(spouse, this);
    //@ assert [1/2]spouse->spouse |-> this;
    this->spouse->spouse = 0;
    //@ close person(spouse, 0);
  }
  free(this); 
}
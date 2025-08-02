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


// TODO: make this function pass the verification
void die(struct person *this)
//@ requires person(this, ?other) &*& (other == 0 ? true : person(other, this));
//@ ensures other == 0 ? true : person(other, 0);
{
  //@ open person(this, other);
  if(this->spouse != 0) {
    //@ assert [1/2]this->spouse |-> ?spouse;
    //@ assert spouse == other;
    //@ assert person(other, this);
    //@ open person(other, this);
    //@ assert [1/2]other->spouse |-> this;
    this->spouse->spouse = 0;
    //@ close person(other, 0);
  }
  free(this); 
}
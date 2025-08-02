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

struct person* person_get_spouse(struct person* this)
//@ requires person(this, ?spouse);
//@ ensures person(this, spouse) &*& result == spouse;
{
  //@ open person(this, spouse);
  struct person* result = this->spouse;
  //@ if (spouse == 0) {
  //@   close person(this, spouse);
  //@ } else {
  //@   close person(this, spouse);
  //@ }
  return result;
}
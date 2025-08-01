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
struct person* person_get_spouse(struct person* this)
//@ requires person(this, ?spouse);
//@ ensures person(this, spouse) &*& result == spouse;
{
  return this->spouse;
}


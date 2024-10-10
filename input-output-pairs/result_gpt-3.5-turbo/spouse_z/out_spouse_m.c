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

struct person *create_person()
//@ requires true;
//@ ensures person(result, 0) &*& result != 0;
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  return p;
}

void marry(struct person *this, struct person *other)
//@ requires person(this, 0) &*& person(other, 0);
//@ ensures person(this, other) &*& person(other, this);
{
  this->spouse = other;
  other->spouse = this;
}

struct person* person_get_spouse(struct person* this)
//@ requires person(this, ?spouse);
//@ ensures person(this, spouse) &*& result == spouse;
{
  return this->spouse;
}

void divorce(struct person* this)
//@ requires person(this, ?other) &*& person(other, this);
//@ ensures person(this, 0) &*& person(other, 0);
{
  this->spouse->spouse = 0;
  this->spouse = 0;
}

void die(struct person *this)
//@ requires person(this, ?other) &*& (other == 0 ? true : person(other, this));
//@ ensures other == 0 ? true : person(other, 0);
{
  if(this->spouse != 0) {
    this->spouse->spouse = 0;
  }
  free(this); 
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  struct person* alice = create_person();
  struct person* bob = create_person();
  struct person* eve = 0;
  marry(alice, bob);
  eve = create_person();
  divorce(bob);
  marry(bob, eve);
  die(alice);
  die(bob);
  die(eve);
  return 0;
}

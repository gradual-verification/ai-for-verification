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


struct person *create_person()
//@ requires true;
//@ ensures person(result, 0);
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
  
  //@ assert person(alice, 0);
  //@ assert person(bob, 0);
  
  marry(alice, bob);
  //@ assert person(alice, bob);
  //@ assert person(bob, alice);
  
  eve = create_person();
  //@ assert person(eve, 0);
  
  divorce(bob);
  //@ assert person(alice, 0);
  //@ assert person(bob, 0);
  
  marry(bob, eve);
  //@ assert person(bob, eve);
  //@ assert person(eve, bob);
  
  die(alice);
  //@ assert person(bob, eve);
  //@ assert person(eve, bob);
  
  die(bob);
  //@ assert person(eve, 0);
  
  die(eve);
  
  return 0;
}
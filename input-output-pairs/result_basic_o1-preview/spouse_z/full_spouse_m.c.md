```c
#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p, struct person *spouse) =
  p != 0 &*& p->name |-> ?name &*& p->spouse |-> spouse &*& malloc_block_person(p);
@*/

struct person *create_person()
//@ requires true;
//@ ensures person(result, 0) &*& result != 0;
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->name = 0; // For simplicity, we're not initializing 'name'.
  p->spouse = 0;
  //@ close person(p, 0);
  return p;
}

void marry(struct person *this, struct person *other)
//@ requires person(this, 0) &*& person(other, 0);
//@ ensures person(this, other) &*& person(other, this);
{
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, other);
  //@ close person(other, this);
}

void divorce(struct person* this)
//@ requires person(this, ?other) &*& (other == 0 ? true : person(other, this));
//@ ensures person(this, 0) &*& (other == 0 ? true : person(other, 0));
{
  if(this->spouse != 0) {
    //@ open person(other, this);
    other->spouse = 0;
    //@ close person(other, 0);
  }
  this->spouse = 0;
  //@ close person(this, 0);
}

void die(struct person *this)
//@ requires person(this, ?other) &*& (other == 0 ? true : person(other, this));
//@ ensures other == 0 ? emp : person(other, 0);
{
  if(this->spouse != 0) {
    //@ open person(other, this);
    other->spouse = 0;
    //@ close person(other, 0);
  }
  //@ open person(this, other);
  free(this);
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  struct person* alice = create_person();
  struct person* bob = create_person();
  struct person* eve;
  marry(alice, bob);
  eve = create_person();
  divorce(bob);
  marry(bob, eve);
  die(alice);
  die(bob);
  die(eve);
  return 0;
}
```

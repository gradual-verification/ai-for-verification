```c CODE and SPEC
#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p, struct person *spouse) =
  p != NULL &*& p->spouse |-> spouse;
@*/

struct person *create_person()
//@ requires true;
//@ ensures person(result, NULL) &*& result != NULL;
{
  struct person *p = malloc(sizeof(struct person));
  if(p == NULL) abort();
  p->spouse = NULL;
  return p;
}

void marry(struct person *this, struct person *other)
//@ requires person(this, NULL) &*& person(other, NULL);
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
//@ ensures person(this, NULL) &*& person(other, NULL);
{
  this->spouse->spouse = NULL;
  this->spouse = NULL;
}

void die(struct person *this)
//@ requires person(this, ?other);
//@ ensures other == NULL ? true : person(other, NULL);
{
  if(this->spouse != NULL) {
    this->spouse->spouse = NULL;
  }
  free(this); 
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  struct person* alice = create_person();
  struct person* bob = create_person();
  struct person* eve = NULL;
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

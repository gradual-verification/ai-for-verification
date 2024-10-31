#include "stdlib.h"

/*@
predicate person(struct person* p; struct person* spouse) =
  p != 0 &*&
  malloc_block_person(p) &*&
  p->name |-> ?name &*&
  p->spouse |-> spouse;
@*/

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate_family_instance malloc_block(struct person* p) =
  person(p, p->spouse);
@*/

/*@
requires true;
ensures person(result, _);
@*/
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  //@ close person(p, 0);
  return p;
}

/*@
requires person(this, _) &*& person(other, _);
ensures person(this, other) &*& person(other, this);
@*/
void marry(struct person *this, struct person *other)
{
  this->spouse = other;
  other->spouse = this;
}

/*@
requires person(this, ?spouse);
ensures person(this, spouse) &*& result == spouse;
@*/
struct person* person_get_spouse(struct person* this)
{
  return this->spouse;
}

/*@
requires person(this, ?spouse) &*& person(spouse, this);
ensures person(this, 0) &*& person(spouse, 0);
@*/
void divorce(struct person* this)
{
  struct person *spouse = this->spouse;
  spouse->spouse = 0;
  this->spouse = 0;
}

/*@
requires person(this, ?spouse);
ensures spouse == 0 ? true : person(spouse, 0);
@*/
void die(struct person *this)
{
  if(this->spouse != 0) {
    this->spouse->spouse = 0;
    //@ close person(this->spouse, 0);
  }
  //@ open person(this, this->spouse);
  free(this);
}

/*@
requires true;
ensures true;
@*/
int main() //@ : main
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

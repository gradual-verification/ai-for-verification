#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p, struct person *spouse) =
  p != 0 &*& p->name |-> _ &*& p->spouse |-> spouse &*& malloc_block_person(p);
@*/

/*
  Weaker Specification:
  - **Description:** Allocates and initializes a new `person` struct with no spouse.
  - **Requires:** No specific preconditions.
  - **Ensures:** The new `person` has no spouse, and the returned pointer is not `0`.
*/
struct person *create_person()
  //@ requires true;
  //@ ensures person(result, 0) &*& result != 0;
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  //@ close person(p, 0);
  return p;
}

/*
  Weaker Specification:
  - **Description:** Marries two `person` instances by setting their spouse pointers to each other.
  - **Requires:** Both `this` and `other` have no spouse.
  - **Ensures:** The two `person` instances are married to each other.
*/
void marry(struct person *this, struct person *other)
  //@ requires person(this, 0) &*& person(other, 0);
  //@ ensures person(this, other) &*& person(other, this);
{
  //@ open person(this, 0);
  //@ open person(other, 0);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, other);
  //@ close person(other, this);
}

/*
  Weaker Specification:
  - **Description:** Retrieves the spouse of the given `person`.
  - **Requires:** The `person` instance is valid.
  - **Ensures:** The returned value is the current spouse of the `person`.
*/
struct person* person_get_spouse(struct person* this)
  //@ requires person(this, ?spouse);
  //@ ensures person(this, spouse) &*& result == spouse;
{
  //@ open person(this, spouse);
  return this->spouse;
  //@ close person(this, spouse);
}

/*
  Weaker Specification:
  - **Description:** Divorces two married `person` instances by setting their spouse pointers to `0`.
  - **Requires:** Both `person` instances are married to each other.
  - **Ensures:** Both `person` instances have no spouse after divorce.
*/
void divorce(struct person* this)
  //@ requires person(this, ?other) &*& person(other, this);
  //@ ensures person(this, 0) &*& person(other, 0);
{
  //@ open person(this, other);
  //@ open person(other, this);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(this, 0);
  //@ close person(other, 0);
}

/*
  Weaker Specification:
  - **Description:** Handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.
  - **Requires:** The `person` instance and their spouse (if any) are valid.
  - **Ensures:** If the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/
void die(struct person *this)
  //@ requires person(this, ?other);
  //@ ensures other == 0 ? true : person(other, 0);
{
  //@ open person(this, other);
  if(this->spouse != 0) {
    this->spouse->spouse = 0;
    //@ close person(this->spouse, 0);
  }
  free(this); 
}

/*
  Weaker Specification:
  - **Description:** Demonstrates creating `person` instances, marrying, divorcing, and handling deaths.
  - **Requires:** No specific preconditions.
  - **Ensures:** The operations on `person` instances are demonstrated, and the program terminates successfully.
*/
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

#include "stdlib.h"

// Forward declaration of predicates
//@ predicate person(struct person *p, char *name, struct person *spouse);

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p, char *name, struct person *spouse) =
  p != 0 &*&
  p->name |-> _ &*&
  p->spouse |-> spouse &*& malloc_block_person(p);
@*/

/***
 * Description:
The `create_person` function allocates and initializes a new `person` struct with no spouse.

@param i - None.
@return - A pointer to the newly created `person` struct.
*/

struct person *create_person()
//@ requires true;
//@ ensures person(result, ?name, 0) &*& result != 0;
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  //@ close person(p, 0, 0);
  return p;
}

/***
 * Description:
The `marry` function marries two unmarried `person` instances by setting their spouse pointers to each other.

@param `this` - Pointer to the first `person`.
@param `other` - Pointer to the second `person`.
*/

void marry(struct person *this, struct person *other)
//@ requires person(this, ?name1, 0) &*& person(other, ?name2, 0);
//@ ensures person(this, name1, other) &*& person(other, name2, this);
{
  //@ open person(this, name1, 0);
  this->spouse = other;
  //@ open person(other, name2, 0);
  other->spouse = this;
  //@ close person(this, name1, other);
  //@ close person(other, name2, this);
}

/***
 * Description:
The `person_get_spouse` function retrieves the spouse of the given `person`.

@param `this` - Pointer to the `person` whose spouse is to be retrieved.
@returns - A pointer to the spouse, or `0` if unmarried.
*/

struct person* person_get_spouse(struct person* this)
//@ requires person(this, ?name, ?spouse);
//@ ensures person(this, name, spouse) &*& result == spouse;
{
  //@ open person(this, name, spouse);
  return this->spouse;
  //@ close person(this, name, spouse);
}

/***
 * Description:
The `divorce` function divorces two married `person` instances by setting their spouse pointers to `0`.

@param `this` - Pointer to one `person` in the marriage.
*/

void divorce(struct person* this)
//@ requires person(this, ?name1, ?spouse) &*& spouse != 0 &*& person(spouse, ?name2, this);
//@ ensures person(this, name1, 0) &*& person(spouse, name2, 0);
{
  //@ open person(this, name1, spouse);
  //@ open person(spouse, name2, this);
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(this, name1, 0);
  //@ close person(spouse, name2, 0);
}

/***
 * Description:
The `die` function handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.

@param `this` - Pointer to the `person` who dies.

It requires that the `person` instance and their spouse (if any) are valid.
It ensures that if the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/

void die(struct person *this)
//@ requires person(this, ?name, ?spouse) &*& (spouse == 0 ? true : person(spouse, ?name2, this));
//@ ensures spouse == 0 ? true : person(spouse, _, 0);
{
  //@ open person(this, name, spouse);
  if(this->spouse != 0) {
    //@ open person(spouse, ?name2, this);
    this->spouse->spouse = 0;
    //@ close person(spouse, name2, 0);
  }
  free(this); 
  // @ leak person(this, _, _);
}

/***
 * Description:
The `main` function demonstrates creating `person` instances, marrying, divorcing, and handling deaths. 
Includes basic operations to test the functionality of the `person` struct and its associated functions.
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

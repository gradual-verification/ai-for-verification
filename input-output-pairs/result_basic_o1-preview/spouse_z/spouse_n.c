#include "stdlib.h"

/*@
predicate person(struct person *p; struct person *spouse) = 
  p != 0 &*&
  malloc_block_person(p) &*&
  p->spouse |-> spouse;
@*/

struct person {
  char* name;
  struct person* spouse;
};

/***
 * Description:
The `create_person` function allocates and initializes a new `person` struct with no spouse.

@param i - None.
@return - A pointer to the newly created `person` struct.
*/
//@ requires true;
//@ ensures result != 0 &*& person(result, 0);
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  //@ malloc_block_person(p);
  p->spouse = 0;
  //@ close person(p, 0);
  return p;
}

/***
 * Description:
The `marry` function marries two `person` instances by setting their spouse pointers to each other.

@param `this` - Pointer to the first `person`.
@param `other` - Pointer to the second `person`.
*/
//@ requires person(this, _) &*& person(other, _);
//@ ensures person(this, other) &*& person(other, this);
void marry(struct person *this, struct person *other)
{
  //@ open person(this, _);
  //@ open person(other, _);
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, other);
  //@ close person(other, this);
}

/***
 * Description:
The `person_get_spouse` function retrieves the spouse of the given `person`.

@param `this` - Pointer to the `person` whose spouse is to be retrieved.
@returns - A pointer to the spouse, or `0` if unmarried.
*/
//@ requires [?f]person(this, ?spouse);
//@ ensures [f]person(this, spouse) &*& result == spouse;
struct person* person_get_spouse(struct person* this)
{
  return this->spouse;
}

/***
 * Description:
The `divorce` function divorces two married `person` instances by setting their spouse pointers to `0`.

@param `this` - Pointer to one `person` in the marriage.
*/
//@ requires person(this, ?spouse) &*& spouse != 0 &*& person(spouse, this);
//@ ensures person(this, 0) &*& person(spouse, 0);
void divorce(struct person* this)
{
  //@ open person(this, spouse);
  //@ open person(spouse, this);
  this->spouse->spouse = 0;
  //@ close person(spouse, 0);
  this->spouse = 0;
  //@ close person(this, 0);
}

/***
 * Description:
The `die` function handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.

@param `this` - Pointer to the `person` who dies.

It requires that the `person` instance and their spouse (if any) are valid.
It ensures that if the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/
//@ requires person(this, ?spouse) &*& (spouse == 0 ? true : person(spouse, this));
//@ ensures spouse == 0 ? true : person(spouse, 0);
void die(struct person *this)
{
  if(this->spouse != 0) {
    //@ open person(spouse, this);
    this->spouse->spouse = 0;
    //@ close person(spouse, 0);
  }
  //@ open person(this, spouse);
  free(this); 
}

/***
 * Description:
The `main` function demonstrates creating `person` instances, marrying, divorcing, and handling deaths. 
Includes basic operations to test the functionality of the `person` struct and its associated functions.
*/
//@ requires true;
//@ ensures true;
int main() //@ : main
{
  struct person* alice = create_person();
  //@ assert person(alice, 0);
  struct person* bob = create_person();
  //@ assert person(bob, 0);
  struct person* eve = 0;
  marry(alice, bob);
  //@ assert person(alice, bob) &*& person(bob, alice);
  eve = create_person();
  //@ assert person(eve, 0);
  divorce(bob);
  //@ assert person(bob, 0) &*& person(alice, 0);
  marry(bob, eve);
  //@ assert person(bob, eve) &*& person(eve, bob);
  die(alice);
  die(bob);
  die(eve);
  return 0;
}

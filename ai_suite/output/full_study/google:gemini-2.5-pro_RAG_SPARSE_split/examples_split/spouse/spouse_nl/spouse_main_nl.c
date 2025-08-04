#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p; struct person *spouse) =
    p->name |-> _ &*&
    p->spouse |-> spouse &*&
    malloc_block_person(p);
@*/


/***
 * Description:
The `create_person` function allocates and initializes a new `person` struct with no spouse.

It makes sure that the return value is a non-null person with its spouse as null. 
*/
struct person *create_person()
    //@ requires true;
    //@ ensures person(result, 0);
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  return p;
}


/***
 * Description:
The `marry` function marries two unmarried `person` instances by setting their spouse pointers to each other.

@param `this` - Pointer to the first `person` whose spouse is null
@param `other` - Pointer to the second `person` whose spouse is null

It makes sure that this and other are married to each other. 
*/
void marry(struct person *this, struct person *other)
    //@ requires person(this, 0) &*& person(other, 0) &*& this != other;
    //@ ensures person(this, other) &*& person(other, this);
{
  this->spouse = other;
  other->spouse = this;
}


/***
 * Description:
The `divorce` function divorces two married `person` instances by setting their spouse pointers to `0`.

@param `this` - Pointer to one `person` in the marriage

It makes sure that `this` person and its original spouse has their spouses as null. 
*/
void divorce(struct person* this)
    //@ requires person(this, ?s) &*& s != 0 &*& person(s, this);
    //@ ensures person(this, 0) &*& person(s, 0);
{
  this->spouse->spouse = 0;
  this->spouse = 0;
}


/***
 * Description:
The `die` function handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.

@param `this` - Pointer to the `person` who dies.

It ensures that if the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/
void die(struct person *this)
    //@ requires person(this, ?s) &*& (s == 0 ? true : person(s, this));
    //@ ensures s == 0 ? true : person(s, 0);
{
  if(this->spouse != 0) {
    this->spouse->spouse = 0;
  }
  free(this); 
}


// TODO: make this function pass the verification
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
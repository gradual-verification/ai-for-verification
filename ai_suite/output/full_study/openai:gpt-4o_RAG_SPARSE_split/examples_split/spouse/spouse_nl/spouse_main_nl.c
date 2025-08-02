#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person* p; struct person* spouse) =
  p->name |-> ?name &*& p->spouse |-> spouse &*& malloc_block_person(p);
@*/

/***
 * Description:
The `create_person` function allocates and initializes a new `person` struct with no spouse.

It makes sure that the return value is a non-null person with its spouse as null. 
*/
/*@
requires true;
ensures result != 0 &*& person(result, 0);
@*/
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  //@ close person(p, 0);
  return p;
}

/***
 * Description:
The `marry` function marries two unmarried `person` instances by setting their spouse pointers to each other.

@param `this` - Pointer to the first `person` whose spouse is null
@param `other` - Pointer to the second `person` whose spouse is null

It makes sure that this and other are married to each other. 
*/
/*@
requires person(this, 0) &*& person(other, 0);
ensures person(this, other) &*& person(other, this);
@*/
void marry(struct person *this, struct person *other)
{
  this->spouse = other;
  other->spouse = this;
  //@ close person(this, other);
  //@ close person(other, this);
}

/***
 * Description:
The `divorce` function divorces two married `person` instances by setting their spouse pointers to `0`.

@param `this` - Pointer to one `person` in the marriage

It makes sure that `this` person and its original spouse has their spouses as null. 
*/
/*@
requires person(this, ?spouse) &*& person(spouse, this);
ensures person(this, 0) &*& person(spouse, 0);
@*/
void divorce(struct person* this)
{
  this->spouse->spouse = 0;
  this->spouse = 0;
  //@ close person(this, 0);
  //@ close person(this->spouse, 0);
}

/***
 * Description:
The `die` function handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.

@param `this` - Pointer to the `person` who dies.

It ensures that if the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/
/*@
requires person(this, ?spouse) &*& (spouse == 0 ? true : person(spouse, this));
ensures spouse == 0 ? true : person(spouse, 0);
@*/
void die(struct person *this)
{
  if(this->spouse != 0) {
    this->spouse->spouse = 0;
    //@ close person(this->spouse, 0);
  }
  free(this); 
}

// TODO: make this function pass the verification
/***
 * Description:
The `main` function demonstrates creating `person` instances, marrying, divorcing, and handling deaths. 
Includes basic operations to test the functionality of the `person` struct and its associated functions.
*/
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
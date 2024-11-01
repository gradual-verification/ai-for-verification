#include "stdlib.h"

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
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  return p;
}

/***
 * Description:
The `marry` function marries two unmarried `person` instances by setting their spouse pointers to each other.

@param `this` - Pointer to the first `person`.
@param `other` - Pointer to the second `person`.
*/
void marry(struct person *this, struct person *other)
{
  this->spouse = other;
  other->spouse = this;
}

/***
 * Description:
The `person_get_spouse` function retrieves the spouse of the given `person`.

@param `this` - Pointer to the `person` whose spouse is to be retrieved.
@returns - A pointer to the spouse, or `0` if unmarried.
*/
struct person* person_get_spouse(struct person* this)
{
  return this->spouse;
}

/***
 * Description:
The `divorce` function divorces two married `person` instances by setting their spouse pointers to `0`.

@param `this` - Pointer to one `person` in the marriage.
*/
void divorce(struct person* this)
{
  this->spouse->spouse = 0;
  this->spouse = 0;
}

/***
 * Description:
The `die` function handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.

@param `this` - Pointer to the `person` who dies.

It requires that the `person` instance and their spouse (if any) are valid.
It ensures that if the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/
void die(struct person *this)
{
  if(this->spouse != 0) {
    this->spouse->spouse = 0;
  }
  free(this); 
}

/***
 * Description:
The `main` function demonstrates creating `person` instances, marrying, divorcing, and handling deaths. 
Includes basic operations to test the functionality of the `person` struct and its associated functions.
*/
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

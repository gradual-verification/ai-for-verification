#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};





/*
  Function `create_person`:
  - Description: Allocates and initializes a new `person` struct with no spouse.
  - Parameters: None.
  - Returns: A pointer to the newly created `person` struct.

*/
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
 
  return p;
}

/*
  **Function `marry`:**
  - **Description:** Marries two `person` instances by setting their spouse pointers to each other.
  - **Parameters:** 
    - `this`: Pointer to the first `person`.
    - `other`: Pointer to the second `person`.
 
*/
void marry(struct person *this, struct person *other)
{

  this->spouse = other;
  other->spouse = this;

}

/*
  Function `person_get_spouse`:
  - Description: Retrieves the spouse of the given `person`.
  - Parameters: 
    - `this`: Pointer to the `person` whose spouse is to be retrieved.
  - Returns:** A pointer to the spouse, or `0` if unmarried.
 
*/
struct person* person_get_spouse(struct person* this)
{

  return this->spouse;
 
}

/*
  Function `divorce`:
  - Description:** Divorces two married `person` instances by setting their spouse pointers to `0`.
  - Parameters:
    - `this`: Pointer to one `person` in the marriage.
*/
void divorce(struct person* this)
{

  this->spouse->spouse = 0;
  this->spouse = 0;
 
}

/*
  Function `die`:
  - Description:** Handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.
  - Parameters:
    - `this`: Pointer to the `person` who dies.
  - Requires: The `person` instance and their spouse (if any) are valid.
  - Ensures: If the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/
void die(struct person *this)
{

  if(this->spouse != 0) {

    this->spouse->spouse = 0;
   
  }
  free(this); 
}

/*
  Function `main`:
  - **Description: Demonstrates creating `person` instances, marrying, divorcing, and handling deaths. Includes basic operations to test the functionality of the `person` struct and its associated functions.
  - Parameters: None.
  - Returns: Always returns `0`.
 
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
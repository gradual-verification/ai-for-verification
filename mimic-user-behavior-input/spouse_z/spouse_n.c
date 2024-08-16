#include "stdlib.h"
#include "spouse.h"

struct person {
  char* name;
  struct person* spouse;
};

/*
  Natural Language Specification:
  - **Description:** This code defines and manipulates a `person` struct that represents an individual with a spouse. The code supports creating individuals, getting their spouse, marrying two individuals, divorcing them, and handling the death of an individual. The specification ensures correct handling of relationships, particularly maintaining mutual spousal links.
  - **Struct `person`:** Represents an individual with a potential spouse.
    - **Fields:**
      - `name`: A pointer to the person's name.
      - `spouse`: A pointer to the spouse, or `0` if unmarried.
*/

/*@
predicate person(struct person *p, struct person *spouse) =
  p != 0 &*& p->name |-> _ &*& (spouse == 0 ? p->spouse |-> 0 : p!=spouse &*& [1/2] p->spouse |-> spouse &<& [1/2] spouse->spouse |-> p) &<&  malloc_block_person(p);
@*/

/*
  **Function `create_person`:**
  - **Description:** Allocates and initializes a new `person` struct with no spouse.
  - **Parameters:** None.
  - **Returns:** A pointer to the newly created `person` struct.
  - **Requires:** No specific preconditions.
  - **Ensures:** The new `person` is not `0`, has no spouse, and the returned pointer is valid.
*/
struct person *create_person()
  //@ requires true;
  //@ ensures person(result, 0) &<& result != 0;
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
  - **Requires:** Both `this` and `other` have no spouse.
  - **Ensures:** The two `person` instances are married to each other, with mutual spouse pointers set.
*/
void marry(struct person *this, struct person *other)
  //@ requires person(this, 0) &<& person(other, 0);
  //@ ensures person(this, other) &<& person(other, this);
{

  this->spouse = other;
  other->spouse = this;

}

/*
  **Function `person_get_spouse`:**
  - **Description:** Retrieves the spouse of the given `person`.
  - **Parameters:** 
    - `this`: Pointer to the `person` whose spouse is to be retrieved.
  - **Returns:** A pointer to the spouse, or `0` if unmarried.
  - **Requires:** The `person` instance is valid.
  - **Ensures:** The `person` remains valid and the returned value is the current spouse.
*/
struct person* person_get_spouse(struct person* this)
  //@ requires person(this, ?spouse);
  //@ ensures person(this, spouse) &<& result == spouse;
{

  return this->spouse;
 
}

/*
  **Function `divorce`:**
  - **Description:** Divorces two married `person` instances by setting their spouse pointers to `0`.
  - **Parameters:** 
    - `this`: Pointer to one `person` in the marriage.
  - **Requires:** Both `person` instances are married to each other.
  - **Ensures:** Both `person` instances are no longer married and have no spouse.
*/
void divorce(struct person* this)
  //@ requires person(this, ?other) &<& person(other, this);
  //@ ensures person(this, 0) &<& person(other, 0);
{

  this->spouse->spouse = 0;
  this->spouse = 0;
 
}

/*
  **Function `die`:**
  - **Description:** Handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.
  - **Parameters:** 
    - `this`: Pointer to the `person` who dies.
  - **Requires:** The `person` instance and their spouse (if any) are valid.
  - **Ensures:** If the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/
void die(struct person *this)

{

  if(this->spouse != 0) {

    this->spouse->spouse = 0;
   
  }
  free(this); 
}

/*
  **Function `main`:**
  - **Description:** Demonstrates creating `person` instances, marrying, divorcing, and handling deaths. Includes basic operations to test the functionality of the `person` struct and its associated functions.
  - **Parameters:** None.
  - **Returns:** Always returns `0`.
  - **Requires:** No specific preconditions.
  - **Ensures:** The operations on `person` instances are demonstrated, and all allocated memory is freed by the end.
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

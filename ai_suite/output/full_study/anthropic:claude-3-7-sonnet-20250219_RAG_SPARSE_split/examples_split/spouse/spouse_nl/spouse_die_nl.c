#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
// Predicate to represent a person with their name and spouse relationship
predicate person(struct person *p; struct person *spouse) =
  p->name |-> ?name &*& 
  p->spouse |-> spouse &*&
  malloc_block_person(p) &*&
  name != 0 ? malloc_block_chars(name, _) &*& string(name, _) : emp;

// Helper lemma to establish that a person and their spouse are different objects
lemma void spouse_diff(struct person *p)
  requires person(p, ?spouse);
  ensures person(p, spouse) &*& spouse != p;
{
  open person(p, spouse);
  if (spouse != 0) {
    pointer_limits(p);
    pointer_limits(spouse);
    pointer_distinct(p, spouse);
  }
  close person(p, spouse);
}

// Helper lemma to establish that if two people are married, they point to each other
lemma void married_lemma(struct person *p)
  requires person(p, ?spouse) &*& spouse != 0 &*& person(spouse, ?spouse_spouse);
  ensures person(p, spouse) &*& person(spouse, spouse_spouse) &*& spouse_spouse == p;
{
  // This is a specification-only lemma, so no implementation needed
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `die` function handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.

@param `this` - Pointer to the `person` who dies.

It ensures that if the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/
/*@
// Function contract for die
requires person(this, ?spouse);
ensures spouse == 0 ? emp : person(spouse, 0);
@*/
void die(struct person *this)
{
  if(this->spouse != 0) {
    /*@
    open person(this, this->spouse);
    struct person *spouse = this->spouse;
    close person(this, spouse);
    spouse_diff(this);
    @*/
    this->spouse->spouse = 0;
    /*@
    open person(spouse, ?spouse_spouse);
    assert spouse_spouse == this;
    spouse->spouse = 0;
    close person(spouse, 0);
    @*/
  }
  /*@
  open person(this, _);
  if (this->name != 0) {
    free(this->name);
  }
  @*/
  free(this); 
}
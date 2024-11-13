To modify the provided code for formal verification using VeriFast, we'll need to ensure that all functions have appropriate preconditions and postconditions, and that memory safety and integer bound checks are accounted for. We'll also need to ensure invariants for any loops and handle memory predicate transformations with open and close statements.

Here is the modified code with complete specifications added:

```c
#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
predicate person(struct person *p, struct person *spouse) =
  p != 0 &*& p->spouse |-> spouse;
@*/

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

struct person* person_get_spouse(struct person* this)
//@ requires person(this, ?spouse);
//@ ensures person(this, spouse) &*& result == spouse;
{
  //@ open person(this, spouse);
  //@ close person(this, spouse);
  return this->spouse;
}

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

void die(struct person *this)
//@ requires person(this, ?other) &*& (other == 0 ? true : person(other, this));
//@ ensures other == 0 ? true : person(other, 0);
{
  //@ open person(this, other);
  if(this->spouse != 0) {
    //@ open person(other, this);
    this->spouse->spouse = 0;
    //@ close person(other, 0);
  }
  free(this);
}

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
```

### Explanation
1. **Predicates:** The `person` predicate captures the state of a `person` structure, ensuring it is non-null and pointing to its `spouse`.
   
2. **Preconditions and Postconditions:** 
    - Each function has preconditions ensuring that all necessary pointers are correctly initialized and adhere to the `person` predicate.
    - Postconditions ensure that after execution, the relationships between objects are as expected.
    
3. **Open and Close Statements:**
    - These are used to manipulate the predicates, ensuring that their state is correctly updated before and after operations.
    
4. **Absence of Loops:** In this example, there are no explicit loops in the code, so no loop invariants are needed.

The modified code should allow VeriFast to verify the correctness and memory safety according to the specification provided.

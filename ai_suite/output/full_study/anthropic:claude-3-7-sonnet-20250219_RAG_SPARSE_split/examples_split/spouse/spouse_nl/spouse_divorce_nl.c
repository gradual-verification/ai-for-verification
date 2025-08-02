#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};


// TODO: make this function pass the verification
/***
 * Description:
The `divorce` function divorces two married `person` instances by setting their spouse pointers to `0`.

@param `this` - Pointer to one `person` in the marriage

It makes sure that `this` person and its original spouse has their spouses as null. 
*/
void divorce(struct person* this)
//@ requires this != 0 &*& this->spouse != 0 &*& this->spouse->spouse == this &*& this->name |-> ?name1 &*& this->spouse->name |-> ?name2;
//@ ensures this != 0 &*& this->spouse |-> 0 &*& this->spouse->spouse |-> 0 &*& this->name |-> name1 &*& this->spouse->name |-> name2;
{
  struct person* spouse = this->spouse;
  spouse->spouse = 0;
  this->spouse = 0;
}
#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};


// TODO: make this function pass the verification
/***
 * Description:
The `die` function handles the death of a `person` by freeing the memory and setting the spouse's spouse pointer to `0` if married.

@param `this` - Pointer to the `person` who dies.

It ensures that if the `person` had a spouse, the spouse's spouse pointer is set to `0`. The `person` instance is freed.
*/
void die(struct person *this)
{
  if(this->spouse != 0) {
    this->spouse->spouse = 0;
  }
  free(this); 
}


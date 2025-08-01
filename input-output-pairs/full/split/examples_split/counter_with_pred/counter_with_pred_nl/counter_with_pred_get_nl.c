#include "stdlib.h"

struct Counter {
  int value;
};


// TODO: make this function pass the verification
/***
 * Description:
The get function gets the values of the given counter.

@param c: pointer to a Counter

The function makes sure that the counter c is unchanged and the return value is the value of c.
*/
int get(struct Counter* c)
{
  int tmp = c->value;
  return tmp;
}


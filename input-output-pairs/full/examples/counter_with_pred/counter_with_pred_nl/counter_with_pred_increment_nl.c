#include "stdlib.h"

struct Counter {
  int value;
};


// TODO: make this function pass the verification
/***
 * Description:
The increment function increments the value of the counter by 1.

@param c: a pointer to a Counter

The function makes sure that the counter has its value incremented by 1.
*/
void increment(struct Counter* c)
{
  int tmp = c->value;
  c->value = tmp + 1;
}


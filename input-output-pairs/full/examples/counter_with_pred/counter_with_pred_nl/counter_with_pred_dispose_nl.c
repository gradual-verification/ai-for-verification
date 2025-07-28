#include "stdlib.h"

struct Counter {
  int value;
};


// TODO: make this function pass the verification
/***
 * Description:
The dispose function frees the memory allocated for the Counter.

@param c: a pointer to a Counter

The function makes sure that the counter c is freed.
*/
void dispose(struct Counter* c)
{
  free(c);
}


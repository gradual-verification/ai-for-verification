#include "stdlib.h"

struct Counter {
  int value;
};

/***
 * Description:
The init function initializes a new Counter structure with the given initial value.
It uses the malloc to allocate the memory for that, if it fails to malloc, the program will terminate.

@param v - the initial value in the Counter.
@requires - none.
*/
struct Counter* init(int v)
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;

  return c;
}
/***
 * Description:
The increment function increments the value of the Counter structure by one.

@param c - a pointer to the Counter structure to be incremented.
@requires - the Counter structure pointed to by c must be initialized, and the incremented value shouldn't overflow.
@ensures - the value of the Counter structure pointed to by c is incremented by one.
*/
void increment(struct Counter* c)
{
  int tmp = c->value;
  c->value = tmp + 1;
}

/***
 * Description:
The dispose function deallocates the memory allocated for the Counter structure.

@param c - a pointer to the Counter structure to be deallocated.
@requires - the Counter structure pointed to by c must have been initialized.
@ensures - the memory allocated for the Counter structure pointed to by c is deallocated.
*/
void dispose(struct Counter* c)
{
  free(c);
}

/***
 * Description:
The swap function swaps the values of two Counter structures.

@param c1 - a pointer to the first Counter structure.
@param c2 - a pointer to the second Counter structure.
@requires - both Counter structures pointed to by c1 and c2 must have been initialized.
@ensures - the values of the Counter structures pointed to by c1 and c2 are swapped.
*/
void swap(struct Counter* c1, struct Counter* c2)
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

/***
 * Description:
The get function retrieves the current value stored in the Counter structure.

@param c - a pointer to the Counter structure.
@return - the current value stored in the Counter structure.
@requires - the Counter structure pointed to by c must have been initialized.
@ensures - the current value stored in the Counter structure is returned.
*/
int get(struct Counter* c)
{
  int tmp = c->value;
  return tmp;
}

/***
 * Description:
The main function initializes two Counter structs with initial values, 
increments one of them, swaps the values between them, 
and then retrieves the value from one of the structs to assert against a known value.
*/
int main() //@ : main
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = get(c2);
  
  dispose(c1); dispose(c2);
  return 0;
}

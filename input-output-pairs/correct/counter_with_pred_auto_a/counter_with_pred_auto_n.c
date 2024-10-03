#include "stdlib.h"

struct Counter {
  int value;
};

/*** 
 * Description:
The init function initializes a new Counter structure with the given initial value.
It uses the malloc to allocate the memory for that, if it fails to malloc, the program will terminate.

@param v - the initial value in the Counter struct.
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
The increment function retrieves the current value from the Counter struct pointed to by c, 
increments it by 1, and updates the value in the struct. 

@param c - the pointer to the Counter struct to be incremented.
*/
void increment(struct Counter* c)
{
  int tmp = c->value;
  c->value = tmp + 1;
}

/***
 * Description:
The dispose function frees the memory allocated for the Counter struct pointed to by c.

@param c - the pointer to the Counter struct to be disposed of.
*/
void dispose(struct Counter* c)
{
  free(c);
}

/*** 
 * Description:
The swap function swaps the values stored in the Counter structs pointed to by c1 and c2.

@param c1 - the pointer to the first Counter struct.
@param c2 - the pointer to the second Counter struct.
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
The get function retrieves and returns the value stored in the Counter struct pointed to by c.

@param c - the pointer to the Counter struct to retrieve the value from.
*/
int get(struct Counter* c)
{
  return c->value;
}

/***
 * Description:
The main function initializes two Counter structs with initial values, 
increments one of them, swaps the values between them, 
and then retrieves the value from one of the structs to assert against a known value.
*/
int main()
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = get(c2);
  assert(tmp == 1);
  
  dispose(c1); dispose(c2);
  return 0;
}
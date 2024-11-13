#include "stdlib.h"

struct Counter {
  int value;
};

// Predicate to represent that Counter is valid
predicate valid_counter(struct Counter* c;) = 
    c != 0  &*& 
    c->value |-> _;

/***
 * Description:
The init function initializes a new Counter structure with the given initial value.
It uses the malloc to allocate the memory for that, if it fails to malloc, the program will terminate.

@param v - the initial value in the Counter.
@ensures - result is a valid Counter with its value initialized to v.
*/
struct Counter* init(int v)
  //@ requires true;
  //@ ensures result != 0 &*& valid_counter(result) &*& result->value |-> v;
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  //@ close valid_counter(c);
  return c;
}

/***
 * Description:
The increment function increments the value of the Counter structure by one.

@param c - a pointer to the Counter structure to be incremented.
@requires - the Counter structure pointed to by c must be initialized.
@ensures - the value of the Counter structure pointed to by c is incremented by one.
*/
void increment(struct Counter* c)
  //@ requires valid_counter(c);
  //@ ensures valid_counter(c) &*& c->value |-> (old(c->value) + 1);
{
  //@ open valid_counter(c);
  c->value = c->value + 1;
  //@ close valid_counter(c);
}

/***
 * Description:
The dispose function deallocates the memory allocated for the Counter structure.

@param c - a pointer to the Counter structure to be deallocated.
@requires - the Counter structure pointed to by c must have been initialized.
@ensures - the memory allocated for the Counter structure pointed to by c is deallocated.
*/
void dispose(struct Counter* c)
  //@ requires valid_counter(c);
  //@ ensures true;
{
  //@ open valid_counter(c);
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
  //@ requires valid_counter(c1) &*& valid_counter(c2);
  //@ ensures valid_counter(c1) &*& valid_counter(c2) &*& c1->value |-> old(c2->value) &*& c2->value |-> old(c1->value);
{
  //@ open valid_counter(c1);
  //@ open valid_counter(c2);
  
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;

  //@ close valid_counter(c1);
  //@ close valid_counter(c2);
}

/***
 * Description:
The get function retrieves the current value stored in the Counter structure.

@param c - a pointer to the Counter structure.
@return - the current value stored in the Counter structure.
@requires - the Counter structure pointed to by c must have been initialized.
@ensures - the returned value is the current value stored in the Counter structure.
*/
int get(struct Counter* c)
  //@ requires valid_counter(c);
  //@ ensures valid_counter(c) &*& result == c->value;
{
  //@ open valid_counter(c);
  return c->value;
  //@ close valid_counter(c);
}

/***
 * Description:
The main function initializes two Counter structs with initial values, 
increments one of them, swaps the values between them, 
and then retrieves the value from one of the structs to assert against a known value.
*/
int main()
  //@ requires true;
  //@ ensures true;
{
  struct Counter* c1 = init(0);
  struct Counter* c2 = init(5);

  increment(c1); 
  swap(c1, c2); 
  int tmp = get(c2);
  
  dispose(c1); 
  dispose(c2);
  return 0;
}

#include "stdlib.h"

struct Counter {
  int value;
};

/*@
// Define a predicate for Counter struct
predicate counter(struct Counter* c; int value) =
    c->value |-> value &*& malloc_block_Counter(c);
@*/

/***
 * Description:
The init function creates a new counter with the given value.

@param v: the given value to be set

The function makes sure that the returned value is an counter whose value is v.
*/
struct Counter* init(int v)
//@ requires true;
//@ ensures counter(result, v);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  //@ close counter(c, v);
  return c;
}


/***
 * Description:
The increment function increments the value of the counter by 1.

@param c: a pointer to a Counter

The function makes sure that the counter has its value incremented by 1.
*/
void increment(struct Counter* c)
//@ requires counter(c, ?v);
//@ ensures counter(c, v + 1);
{
  //@ open counter(c, v);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close counter(c, v + 1);
}


/***
 * Description:
The decrement function decrements the value of the counter by 1.

@param c: a pointer to a Counter

The function makes sure that the counter has its value decremented by 1.
*/
void decrement(struct Counter* c)
//@ requires counter(c, ?v);
//@ ensures counter(c, v - 1);
{
  //@ open counter(c, v);
  int tmp = c->value;
  c->value = tmp - 1;
  //@ close counter(c, v - 1);
}


/***
 * Description:
The dispose function frees the memory allocated for the Counter.

@param c: a pointer to a Counter

The function makes sure that the counter c is freed.
*/
void dispose(struct Counter* c)
//@ requires counter(c, ?v);
//@ ensures true;
{
  //@ open counter(c, v);
  free(c);
}


/***
 * Description:
The swap function swaps the values of the two Counters.

@param c1, c2: pointers to two Counter

The function makes sure that the two counters have their values swapped.
*/
void swap(struct Counter* c1, struct Counter* c2)
//@ requires counter(c1, ?v1) &*& counter(c2, ?v2);
//@ ensures counter(c1, v2) &*& counter(c2, v1);
{
  //@ open counter(c1, v1);
  //@ open counter(c2, v2);
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  //@ close counter(c1, v2);
  //@ close counter(c2, v1);
}


/***
 * Description:
The get function gets the values of the given counter.

@param c: pointer to a Counter

The function makes sure that the counter c is unchanged and the return value is the value of c.
*/
int get(struct Counter* c)
//@ requires counter(c, ?v);
//@ ensures counter(c, v) &*& result == v;
{
  //@ open counter(c, v);
  int tmp = c->value;
  //@ close counter(c, v);
  return tmp;
}


/***
 * Description:
The random function generates a random boolean value.

The function does not modify the state of any variables, and we don't need to implement it.
*/
bool my_random();
//@ requires true;
//@ ensures true;


// TODO: make this function pass the verification
/***
 * Description:
The main2 function tests the operations of Counter with loops.
*/
int main2() 
//@ requires true;
//@ ensures true;
{
  struct Counter* c = init(0);
  bool b = my_random();
  int n = 0;
  
  /*@
  // Loop invariant for the first loop
  invariant counter(c, n) &*& 0 <= n &*& n <= INT_MAX;
  decreases INT_MAX - n + (b ? 1 : 0);
  @*/
  while(b && n < INT_MAX) 
  {
    increment(c);
    n = n + 1;
    b = my_random();
  }

  /*@
  // Loop invariant for the second loop
  invariant counter(c, n) &*& 0 <= n;
  decreases n;
  @*/
  while(0 < n) 
  {
    decrement(c);
    n = n - 1;
  }
  dispose(c);
  return 0;
}
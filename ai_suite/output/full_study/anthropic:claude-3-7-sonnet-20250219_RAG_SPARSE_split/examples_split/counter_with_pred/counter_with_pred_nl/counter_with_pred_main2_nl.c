#include "stdlib.h"

/*@
predicate counter(struct Counter* c; int value) =
    c->value |-> value &*& malloc_block_Counter(c);
@*/

struct Counter {
  int value;
};

/***
 * Description:
The init function creates a new counter with the given value.

@param v: the given value to be set

The function makes sure that the returned value is an counter whose value is v.
*/
//@ ensures counter(result, v);
struct Counter* init(int v)
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
//@ requires counter(c, ?v);
//@ ensures counter(c, v + 1);
void increment(struct Counter* c)
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
//@ requires counter(c, ?v);
//@ ensures counter(c, v - 1);
void decrement(struct Counter* c)
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
//@ requires counter(c, ?v);
//@ ensures true;
void dispose(struct Counter* c)
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
//@ requires counter(c1, ?v1) &*& counter(c2, ?v2);
//@ ensures counter(c1, v2) &*& counter(c2, v1);
void swap(struct Counter* c1, struct Counter* c2)
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
//@ requires counter(c, ?v);
//@ ensures counter(c, v) &*& result == v;
int get(struct Counter* c)
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
//@ ensures true;
bool random();


// TODO: make this function pass the verification
/***
 * Description:
The main2 function tests the operations of Counter with loops.
*/
//@ requires true;
//@ ensures true;
int main2() 
{
  struct Counter* c = init(0);
  bool b = random();
  int n = 0;
  
  /*@
  invariant counter(c, n) &*& n >= 0;
  @*/
  while(b && n < INT_MAX) 
  {
    increment(c);
    n = n + 1;
    b = random();
  }

  /*@
  invariant counter(c, n - ?m) &*& 0 <= m &*& m <= n;
  decreases m;
  @*/
  while(0 < n) 
  {
    decrement(c);
    n = n - 1;
  }
  dispose(c);
  return 0;
}
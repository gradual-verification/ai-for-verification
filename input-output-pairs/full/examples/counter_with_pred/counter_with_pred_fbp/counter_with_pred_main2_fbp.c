#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/


void decrement(struct Counter* c)
  //@ requires Counter(c, ?v) &*& v > INT_MIN;
  //@ ensures Counter(c, v - 1);
{
  int tmp = c->value;
  c->value = tmp - 1;
}


void dispose(struct Counter* c)
  //@ requires Counter(c, _);
  //@ ensures true;
{
  free(c);
}


bool random();
//@ requires true;
//@ ensures true;


struct Counter* init(int v)
  //@ requires true;
  //@ ensures Counter(result, v);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;

  return c;
}


void increment(struct Counter* c)
  //@ requires Counter(c, ?v) &*& v < INT_MAX;
  //@ ensures Counter(c, v+1);
{
  int tmp = c->value;
  c->value = tmp + 1;
}


// TODO: make this function pass the verification
int main2() 
//@ requires true;
//@ ensures true;
{
  struct Counter* c = init(0);
  bool b = random();
  int n = 0;
  // split of an arbitrary number of children
  while(b && n < INT_MAX) 
  {
    increment(c);
    n = n + 1;
    b = random();
  }

  // put the permission back together
  while(0<n) 
  //@ invariant 0<=n &*& Counter(c, n);
  {
    decrement(c);
    n = n - 1;
  }
  dispose(c);
  return 0;
}

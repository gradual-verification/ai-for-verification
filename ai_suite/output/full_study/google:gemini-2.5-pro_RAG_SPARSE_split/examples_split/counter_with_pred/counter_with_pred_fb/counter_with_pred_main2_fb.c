#include "stdlib.h"

struct Counter {
  int value;
};

/*@
// The predicate is updated to include the malloc_block chunk.
// This is crucial for proving memory safety when calling free().
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/


struct Counter* init(int v)
  //@ requires true;
  //@ ensures Counter(result, v);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  //@ close Counter(c, v);
  return c;
}


void increment(struct Counter* c)
  //@ requires Counter(c, ?v) &*& v < INT_MAX;
  //@ ensures Counter(c, v+1);
{
  //@ open Counter(c, v);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close Counter(c, v + 1);
}


void decrement(struct Counter* c)
  //@ requires Counter(c, ?v) &*& v > INT_MIN;
  //@ ensures Counter(c, v - 1);
{
  //@ open Counter(c, v);
  int tmp = c->value;
  c->value = tmp - 1;
  //@ close Counter(c, v - 1);
}


void dispose(struct Counter* c)
  //@ requires Counter(c, _);
  //@ ensures true;
{
  //@ open Counter(c, _);
  free(c);
}


void swap(struct Counter* c1, struct Counter* c2)
  //@ requires Counter(c1, ?v1) &*& Counter(c2, ?v2);
  //@ ensures Counter(c1, v2) &*& Counter(c2, v1);
{
  //@ open Counter(c1, v1);
  //@ open Counter(c2, v2);
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  //@ close Counter(c1, v2);
  //@ close Counter(c2, v1);
}


int get(struct Counter* c)
  //@ requires Counter(c, ?v);
  //@ ensures Counter(c, v) &*& result==v;
{
  //@ open Counter(c, v);
  int tmp = c->value;
  //@ close Counter(c, v);
  return tmp;
}



bool random();
//@ requires true;
//@ ensures true;


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
    // The invariant states that the counter's value is always equal to 'n'.
    //@ invariant Counter(c, n) &*& 0 <= n &*& n <= INT_MAX;
  {
    increment(c);
    n = n + 1;
    b = random();
  }

  // put the permission back together
  while(0 < n)
    // The invariant here is similar, ensuring the counter's value is 'n' as it's decremented.
    //@ invariant Counter(c, n) &*& 0 <= n;
  {
    decrement(c);
    n = n - 1;
  }
  
  // After the second loop, 'n' must be 0.
  // Therefore, we have Counter(c, 0), which allows us to dispose of it.
  dispose(c);
  return 0;
}
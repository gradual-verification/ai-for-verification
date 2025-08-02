#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block(c, sizeof(struct Counter));
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
  //@ close Counter(c, v+1);
}

void decrement(struct Counter* c)
  //@ requires Counter(c, ?v) &*& v > INT_MIN;
  //@ ensures Counter(c, v - 1);
{
  //@ open Counter(c, v);
  int tmp = c->value;
  c->value = tmp - 1;
  //@ close Counter(c, v-1);
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
    //@ invariant Counter(c, n);
  {
    increment(c);
    n = n + 1;
    b = random();
  }

  // put the permission back together
  while(0<n) 
    //@ invariant Counter(c, n);
  {
    decrement(c);
    n = n - 1;
  }
  dispose(c);
  return 0;
}
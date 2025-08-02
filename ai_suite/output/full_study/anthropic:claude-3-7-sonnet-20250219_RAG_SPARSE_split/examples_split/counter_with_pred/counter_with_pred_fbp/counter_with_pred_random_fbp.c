#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/


bool random()
//@ requires true;
//@ ensures true;
{
    // Since the function is annotated with "requires true" and "ensures true",
    // it doesn't need to maintain any specific state or guarantee any specific result.
    // We can simply return any boolean value.
    return true;
}

struct Counter* create_counter()
  //@ requires true;
  //@ ensures Counter(result, 0);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) abort();
  c->value = 0;
  //@ close Counter(c, 0);
  return c;
}

void inc(struct Counter* c)
  //@ requires Counter(c, ?v);
  //@ ensures Counter(c, v + 1);
{
  //@ open Counter(c, v);
  c->value = c->value + 1;
  //@ close Counter(c, v + 1);
}

void swap(struct Counter* c1, struct Counter* c2)
  //@ requires Counter(c1, ?v1) &*& Counter(c2, ?v2);
  //@ ensures Counter(c1, v2) &*& Counter(c2, v1);
{
  //@ open Counter(c1, v1);
  //@ open Counter(c2, v2);
  int temp = c1->value;
  c1->value = c2->value;
  c2->value = temp;
  //@ close Counter(c1, v2);
  //@ close Counter(c2, v1);
}

int counter_get(struct Counter* c)
  //@ requires Counter(c, ?v);
  //@ ensures Counter(c, v) &*& result == v;
{
  //@ open Counter(c, v);
  int result = c->value;
  //@ close Counter(c, v);
  return result;
}

void dispose(struct Counter* c)
  //@ requires Counter(c, ?v);
  //@ ensures true;
{
  //@ open Counter(c, v);
  free(c);
}
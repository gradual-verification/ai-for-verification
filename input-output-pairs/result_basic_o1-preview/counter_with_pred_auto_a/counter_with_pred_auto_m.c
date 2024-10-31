#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c; int v) =
  c->value |-> v;
@*/

struct Counter* init(int v)
//@ requires emp;
//@ ensures Counter(result, v) &*& malloc_block_Counter(result);
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
//@ requires Counter(c, ?v);
//@ ensures Counter(c, v + 1);
{
  //@ open Counter(c, v);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close Counter(c, v + 1);
}

void dispose(struct Counter* c)
//@ requires Counter(c, _) &*& malloc_block_Counter(c);
//@ ensures emp;
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
//@ ensures Counter(c, v) &*& result == v;
{
  //@ open Counter(c, v);
  int val = c->value;
  //@ close Counter(c, v);
  return val;
}

int main() //@ : main
//@ requires emp;
//@ ensures emp;
{
  struct Counter* c1 = init(0);
  //@ assert Counter(c1, 0) &*& malloc_block_Counter(c1);
  struct Counter* c2 = init(5);
  //@ assert Counter(c2, 5) &*& malloc_block_Counter(c2);

  increment(c1);
  //@ assert Counter(c1, 1);

  swap(c1, c2);
  //@ assert Counter(c1, 5) &*& Counter(c2, 1);

  int tmp = get(c2);
  //@ assert tmp == 1;
  assert(tmp == 1);

  dispose(c1);
  dispose(c2);
  return 0;
}

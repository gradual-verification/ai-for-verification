#include "stdlib.h"

struct Counter {
  int value;
};

struct Counter* init(int v)
  //@ requires true;
  //@ ensures result->value |-> v;
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  return c;
}

void increment(struct Counter* c)
  //@ requires c->value |-> ?v;
  //@ ensures c->value |-> v + 1;
{
  int tmp = c->value;
  c->value = tmp + 1;
  //int tmp = c->value;
  //if (tmp == INT_MAX) {
    //abort();  
  //}
  //c->value = tmp + 1;
}

void dispose(struct Counter* c)
  //@ requires true;
  //@ ensures true;
{
  free(c);
}

void swap(struct Counter* c1, struct Counter* c2)
  //@ requires c1->value |-> ?v1 &*& c2->value |-> ?v2;
  //@ ensures c1->value |-> v2 &*& c2->value |-> v1;
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = c2->value;
  dispose(c1); dispose(c2);
  return 0;
}

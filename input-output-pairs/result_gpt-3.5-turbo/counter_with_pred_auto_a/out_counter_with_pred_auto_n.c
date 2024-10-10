#include "stdlib.h"

struct Counter {
  int value;
};

//@malloc_dynamic_allocation(struct Counter *)
//@requires \valid(v)
//@ensures \result != NULL
struct Counter* init(int v);

//@requires \valid(c)
//@requires \mutable(c)
//@ensures c->value == \old(c->value) + 1
void increment(struct Counter* c);

//@requires \valid(c)
//@ensures \free(c)
void dispose(struct Counter* c);

//@requires \valid(c1) && \valid(c2)
//@requires \mutable(c1) && \mutable(c2)
//@ensures c1->value == \old(c2->value) && c2->value == \old(c1->value)
void swap(struct Counter* c1, struct Counter* c2);

//@requires \valid(c)
int get(struct Counter* c);

int main()
{
  struct Counter* c1 = init(0); 
  struct Counter* c2 = init(5);

  increment(c1); 
  swap(c1, c2); 
  int tmp = get(c2);
  
  assert(tmp == 1);
  
  dispose(c1); 
  dispose(c2);
  
  return 0;
}

#include "stdlib.h"

struct cell {
  int x;
};

/*@
predicate cell(struct cell* c, int v) =
  c->x |-> v &*& malloc_block_cell(c);
@*/

struct cell* create_cell() 
  //@ requires true;
  //@ ensures cell(result, 0);
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) abort();
  c->x = 0;

  return c;
}

void cell_set(struct cell* c, int v)
  //@ requires cell(c, _);
  //@ ensures cell(c, v);
{

  c->x = v;

}

void cell_inc(struct cell* c, int v)
  //@ requires cell(c, ?x) &*& INT_MIN - v <= x &*& x <= INT_MAX - v;
  //@ ensures cell(c, x + v);
{

  c->x += v;

}

int cell_get(struct cell* c)
  //@ requires cell(c, ?v);
  //@ ensures cell(c, v) &*& result == v;
{

  return c->x;

}

void cell_swap(struct cell* c1, struct cell* c2)
  //@ requires cell(c1, ?v1) &*& cell(c2, ?v2);
  //@ ensures cell(c1, v2) &*& cell(c2, v1);
{
  int tmp1 = cell_get(c1);
  int tmp2 = cell_get(c2);
  cell_set(c1, tmp2);
  cell_set(c2, tmp1);
}

void cell_dispose(struct cell* c) 
  //@ requires cell(c, _);
  //@ ensures true;
{

  free(c);
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct cell* c1 = create_cell();
  struct cell* c2 = create_cell();
  
  cell_set(c1, 5);
  cell_set(c2, 10);
  
  cell_swap(c1, c2); 
  
  int tmp = cell_get(c1);
  assert(tmp == 10);
  
  cell_dispose(c1);
  cell_dispose(c2);
  
  return 0;
}
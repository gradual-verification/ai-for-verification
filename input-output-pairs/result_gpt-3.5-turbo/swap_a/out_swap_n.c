#include "stdlib.h"
#include <stdbool.h>

//@ predicate point(struct point *p; int x, int y) = p != NULL &*& p->x |-> x &*& p->y |-> y;

//@ predicate swap(int *a, int *b, int x, int y) = a != NULL &*& b != NULL &*& *a |-> x &*& *b |-> y;

void swap(int *a, int *b)
  //@ requires swap(a, b, ?x, ?y);
  //@ ensures swap(a, b, y, x);
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

struct point {
  int x;
  int y;
};

void point_mirror(struct point *p)
  //@ requires point(p, ?x, ?y);
  /*@ ensures 
      swap(&p->x, &p->y, x, y) &*& 
      point(p, y, x);
  @*/
{
  //@ open point(p, _, _);
  swap(&p->x, &p->y);
  //@ close point(p, y, x);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct point *p = malloc(sizeof(struct point));
  if (p == 0) { abort(); }
  p->x = 3;
  p->y = 10;
  //@ close point(p, 3, 10);
  point_mirror(p);
  //@ open point(p, _, _);
  bool b = p->x == 10 && p->y == 3;
  assert(b);
  //@ close point(p, 10, 3);
  free(p);
  return 0;
}

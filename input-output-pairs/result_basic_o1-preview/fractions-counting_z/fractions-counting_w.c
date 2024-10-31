#include "stdlib.h"

/*@

predicate c_valid(struct C* c, int x) = c->x |-> x;

predicate counter(struct C* c, int x, int nbTickets) = c_valid(c, x) &*& nbTickets >= 0;

predicate ticket(struct C* c, int x);

@*/

struct C {
  int x;
};

struct C* create_C(int x) 
//@ requires true;
//@ ensures c_valid(result, x);
{
  struct C* c = malloc(sizeof(struct C));
  if(c==0) {
    abort();
  } 
  c->x = x;
  return c;
}

void create_counter(struct C* c)
//@ requires c_valid(c, ?x);
//@ ensures counter(c, x, 0);
{
  // No code needed; handled by predicate definitions
}

void create_ticket(struct C* c)
//@ requires counter(c, ?x, ?nbTickets);
//@ ensures counter(c, x, nbTickets + 1) &*& ticket(c, x);
{
  //@ nbTickets >= 0;
}

void dispose_ticket(struct C* c)
//@ requires counter(c, ?x, ?nbTickets) &*& ticket(c, x) &*& nbTickets > 0;
//@ ensures counter(c, x, nbTickets -1);
{
  //@ nbTickets >= 1;
}

void dispose_counter(struct C* c)
//@ requires counter(c, ?x, 0);
//@ ensures c_valid(c, x);
{
  // No code needed; handled by predicate definitions
}

bool random();
//@ requires true;
//@ ensures true;

int main()
//@ requires true;
//@ ensures true;
{
  struct C* c = create_C(5);
  //@ int x = 5;
  create_counter(c);
  bool b = random();
  int n = 0;
  while(b && n < INT_MAX)
    //@ invariant counter(c, x, n) &*& n >= 0;
  {
    create_ticket(c);
    n = n + 1;
    b = random();
  }

  while(0 < n)
    //@ invariant counter(c, x, n) &*& n >= 0;
  {
    dispose_ticket(c);
    n = n -1;
  }
  dispose_counter(c);
  //@ c_valid(c, x);
  free(c);
  return 0;
}

int main2()
//@ requires true;
//@ ensures true;
{
  struct C* c = create_C(3);
  //@ int x = 3;
  create_counter(c);
  create_ticket(c);
  dispose_ticket(c);
  dispose_counter(c);
  //@ c_valid(c, x);
  free(c);
  return 0;
}

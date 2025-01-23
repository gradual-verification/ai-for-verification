#include "stdlib.h"
#include "stdbool.h"

/*@
predicate C(struct C* c; int x) =
    c->x |-> x;

predicate counter(struct C* c, int n;) =
    C(c, ?x) &*& 0 <= n;

predicate tickets(struct C* c, int n;) =
    0 <= n;

@*/

struct C {
  int x;
};

// Create a struct C and initialize its x field to the given value

struct C* create_C(int x) 
//@ requires true;
//@ ensures C(result, x) &*& malloc_block_C(result);
{
  struct C* c = malloc(sizeof(struct C));
  if(c==0) {
    abort();
  } 
  c->x = x;
  return c;
}

// Create a counter predicate to show that no tickets exist yet

void create_counter(struct C* c)
//@ requires C(c, ?x);
//@ ensures counter(c, 0);
{
}

// Modify the predicates to create a new ticket

void create_ticket(struct C* c)
//@ requires counter(c, ?n);
//@ ensures counter(c, n + 1) &*& tickets(c, n + 1);
{
  //@ close counter(c, n + 1);
}

// Modify the predicates to dispose of a ticket

void dispose_ticket(struct C* c)
//@ requires counter(c, ?n) &*& tickets(c, n) &*& 0 < n;
//@ ensures counter(c, n - 1) &*& tickets(c, n - 1);
{
  //@ close counter(c, n - 1);
}

// Consume the counter predicate showing all tickets are disposed

void dispose_counter(struct C* c)
//@ requires counter(c, 0);
//@ ensures C(c, ?x);
{
}

// A stub for the random boolean generator

bool random();
//@ requires true;
//@ ensures true;

// Main program function to test the components

int main()
//@ requires true;
//@ ensures true;
{
  struct C* c = create_C(5);
  create_counter(c);
  bool b = random();
  int n = 0;
  while(b && n < INT_MAX)
  /*@
  invariant counter(c, n) &*& tickets(c, n) &*& 0 <= n;
  @*/
  {
    create_ticket(c);
    n = n + 1;
    b = random();
  }

  while(0<n) 
  /*@
  invariant counter(c, n) &*& tickets(c, n) &*& 0 <= n;
  @*/
  {
    dispose_ticket(c);
    n = n - 1;
  }
  
  dispose_counter(c);
  free(c);
  return 0;
}

// Simplified main to specifically test components

int main2()
//@ requires true;
//@ ensures true;
{
  struct C* c = create_C(3);
  create_counter(c);
  create_ticket(c);
  dispose_ticket(c);
  dispose_counter(c);
  free(c);
  return 0;
}

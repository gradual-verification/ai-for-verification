#include "stdlib.h"
#include "limits.h"

struct C {
  int x;
};

struct C* create_C(int x) 
//@ requires emp;
//@ ensures result != 0 &*& result->x |-> x &*& malloc_block_C(result);
{
  struct C* c = malloc(sizeof(struct C));
  if(c == 0) {
    abort();
  } 
  c->x = x;
  return c;
}

/*@
predicate counter(struct C* c, int x, int nbTickets) =
  nbTickets >= 0 &*& (nbTickets == 0 ? [1.0] c->x |-> x : [0.5] c->x |-> x) &*& malloc_block_C(c);

predicate tickets(struct C* c, int x, int howMany) =
  howMany <= 0 ? emp : [0.5] c->x |-> x;
@*/

void create_counter(struct C* c)
//@ requires c->x |-> ?x &*& malloc_block_C(c);
//@ ensures counter(c, x, 0);
{
  //@ close counter(c, x, 0);
}

void create_ticket(struct C* c)
//@ requires counter(c, ?x, ?nbTickets) &*& tickets(c, x, nbTickets);
//@ ensures counter(c, x, nbTickets + 1) &*& tickets(c, x, nbTickets + 1);
{
  //@ open counter(c, x, nbTickets);
  //@ close counter(c, x, nbTickets + 1);
  //@ open tickets(c, x, nbTickets);
  //@ close tickets(c, x, nbTickets + 1);
}

void dispose_ticket(struct C* c)
//@ requires counter(c, ?x, ?nbTickets) &*& tickets(c, x, nbTickets) &*& nbTickets > 0;
//@ ensures counter(c, x, nbTickets - 1) &*& tickets(c, x, nbTickets - 1);
{
  //@ open tickets(c, x, nbTickets);
  //@ open counter(c, x, nbTickets);
  //@ close counter(c, x, nbTickets - 1);
  //@ close tickets(c, x, nbTickets - 1);
}

void dispose_counter(struct C* c)
//@ requires counter(c, ?x, 0);
//@ ensures [1.0]c->x |-> x &*& malloc_block_C(c);
{
  //@ open counter(c, x, 0);
}

bool random();
//@ requires emp;
//@ ensures emp;

int main() 
//@ requires emp;
//@ ensures emp;
{
  struct C* c = create_C(5);
  create_counter(c);
  bool b = random();
  int n = 0;
  //@ close tickets(c, 5, 0);
  while(b && n < INT_MAX) 
  /*@
  invariant counter(c, 5, n) &*& tickets(c, 5, n) &*& 0 <= n;
  @*/
  {
    create_ticket(c);
    n = n + 1;
    b = random();
  }

  while(0 < n) 
  /*@
  invariant counter(c, 5, n) &*& tickets(c, 5, n) &*& 0 <= n;
  @*/
  {
    dispose_ticket(c);
    n = n - 1;
  }
  dispose_counter(c);
  free(c);
  return 0;
  //@ open tickets(c, 5, 0);
}

int main2()
//@ requires emp;
//@ ensures emp;
{
  struct C* c = create_C(3);
  create_counter(c);
  //@ close tickets(c, 3, 0);
  create_ticket(c);
  dispose_ticket(c);
  dispose_counter(c);
  free(c);
  return 0;
  //@ open tickets(c, 3, 0);
}

#include "stdlib.h"

struct C {
  int x;
};
//remove the malloc block
struct C* create_C(int x) 
  //@ requires true;
  //@ ensures result->x |-> x 
{
  struct C* c = malloc(sizeof(struct C));
  if (c == 0) {
    abort();
  } 
  c->x = x;
  return c;
}

/*@
predicate counter(struct C* c, int x);

predicate ticket(struct C* c);

lemma void create_counter(struct C* c);
  requires c->x |-> ?x;
  ensures counter(c, x);

lemma void create_ticket(struct C* c);
  requires counter(c, ?x);
  ensures counter(c, x) &*& ticket(c) &*& c->x |-> x;

lemma void dispose_ticket(struct C* c);
  requires counter(c, ?x) &*& ticket(c) &*& c->x |-> x;
  ensures counter(c, x);

lemma void dispose_counter(struct C* c);
  requires counter(c, ?x);
  ensures c->x |-> x;
@*/



int main() 
  //@ requires true;
  //@ ensures true;
{
  struct C* c = create_C(5);

  bool b = random();
  int n = 0;
  while (b) 
   
  {
    
    n = n + 1;
    b = random();
  }

  while (n > 0) 

  {
 
    n = n - 1;
  }

  free(c);
  return 0;
}

int main2()
//@ requires emp;
//@ ensures emp;
{
  struct C* c = create_C(3);
 
  free(c);
  return 0;
}

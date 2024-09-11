#include "stdlib.h"

struct C {
  int x;
};

struct C* create_C(int x) 

{
  struct C* c = malloc(sizeof(struct C));
  if(c==0) {
    abort();
  } 
  c->x = x;
  return c;
}

/*@

predicate counter(struct C* c, int x, int id, real frac, int nbTickets);

predicate ticket(struct C* c, int id, real frac);

lemma void create_counter(struct C* c);
  requires [?f]c->x |-> ?x;
  ensures counter(c, x, ?id, f, 0);

lemma void create_ticket(struct C* c);
  requires counter(c, ?x, ?id, ?f, ?i);
  ensures counter(c, x, id, f, i + 1) &*& ticket(c, id, ?f2) &*& [f2]c->x |-> x;

lemma void dispose_ticket(struct C* c);
  requires counter(c, ?x, ?id, ?f, ?i) &*& ticket(c, id, ?f2) &*& [f2]c->x |-> x;
  ensures counter(c, x, id, f, i - 1);

lemma void dispose_counter(struct C* c);
  requires counter(c, ?x, ?id, ?f, 0);
  ensures [f]c->x |-> x;
@*/

bool random();
//@ requires emp;
//@ ensures emp;

int main() 
  //@ requires emp;
  //@ ensures emp;
{
  struct C* c = create_C(5);

  bool b = random();
  int n = 0;

  while(b) 
   
  {
    ;
    n = n + 1;
   
    b = random();
  }


  while(0<n) 
   
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



```c
#include "stdlib.h"
#include <limits.h>

struct C {
  int x;
  //@ int count;
};

//@ predicate struct_C(struct C* c;) = c->x |-> _ &*& c->count |-> _;

//@ predicate counter(struct C* c; int n) = c->x |-> _ &*& c->count |-> n &*& n >= 0;

struct C* create_C(int x) 
/*@ requires true;
    ensures struct_C(result); @*/
{
  struct C* c = malloc(sizeof(struct C));
  if(c==0) {
    abort();
  } 
  c->x = x;
  //@ c->count = 0; // Initialize ghost field
  return c;
}

void create_counter(struct C* c)
/*@ requires struct_C(c);
    ensures counter(c, 0); @*/
{
  //@ open struct_C(c);
  //@ c->count = 0; // Initialize count to 0, although it was already set in create_C
  //@ close counter(c, 0);
}

void create_ticket(struct C* c)
/*@ requires counter(c, ?n);
    ensures counter(c, n + 1); @*/
{
  //@ open counter(c, n);
  //@ c->count = n + 1;
  //@ close counter(c, n + 1);
}

void dispose_ticket(struct C* c)
/*@ requires counter(c, ?n) &*& n > 0;
    ensures counter(c, n - 1); @*/
{
  //@ open counter(c, n);
  //@ c->count = n - 1;
  //@ close counter(c, n - 1);
}

void dispose_counter(struct C* c)
/*@ requires counter(c, 0);
    ensures struct_C(c); @*/
{
  //@ open counter(c, 0);
  //@ close struct_C(c);
}

bool random();
/*@ requires true;
    ensures true; @*/

int main()
/*@ requires true;
    ensures true; @*/
{
  struct C* c = create_C(5);
  create_counter(c);
  bool b = random();
  int n = 0;
  while(b && n < INT_MAX) 
  /*@ invariant counter(c, n) &*& n >= 0;
      decreases INT_MAX - n; @*/
  {
    create_ticket(c);
    n = n + 1;
    b = random();
  }

  while(0 < n) 
  /*@ invariant counter(c, n) &*& n >= 0;
      decreases n; @*/
  {
    dispose_ticket(c);
    n = n - 1;
  }
  dispose_counter(c);
  free(c);
  return 0;
}

int main2()
/*@ requires true;
    ensures true; @*/
{
  struct C* c = create_C(3);
  create_counter(c);
  create_ticket(c);
  dispose_ticket(c);
  dispose_counter(c);
  free(c);
  return 0;
}
```

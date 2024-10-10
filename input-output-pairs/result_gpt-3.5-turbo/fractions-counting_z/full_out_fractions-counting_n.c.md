```c CODE and SPEC
#include "stdlib.h"

struct C {
  int x;
};

//@ predicate ticket();

//@ predicate counter();

struct C* create_C(int x)
  //@ requires true;
  //@ ensures result->x == x &*& ticket(result) &*& counter(result);
{
  struct C* c = malloc(sizeof(struct C));
  if(c == 0) abort();
  c->x = x;
  //@ close ticket();
  //@ close counter();
  
  return c;
}

void create_counter(struct C* c)
  //@ requires c->x |-> ?x &*& ticket() &*& counter();
  //@ ensures c->x |-> x &*& counter() &*& ticket();
{
  // No operation needed
}

void create_ticket(struct C* c)
  //@ requires c->x |-> ?x &*& ticket() &*& counter();
  //@ ensures c->x |-> x &*& ticket() &*& counter();
{
  // Increment ticket
  //@ open ticket();
  //@ close ticket();
}

void dispose_ticket(struct C* c)
  //@ requires c->x |-> ?x &*& ticket();
  //@ ensures c->x |-> x &*& ticket();
{
  // Decrement ticket
  //@ open ticket();
  //@ close ticket();
}

void dispose_counter(struct C* c)
  //@ requires c->x |-> ?x &*& counter();
  //@ ensures c->x |-> x;
{
  // Dispose counter
}

bool random()
  //@ requires true;
  //@ ensures true;
{
  // Dummy random function
  return true;
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct C* c = create_C(5);
  create_counter(c);
  bool b = random();
  int n = 0;

  while(b && n < INT_MAX)
    //@ invariant c->x |-> 5 &*& ticket() &*& counter();
  {
    create_ticket(c);
    //@ open ticket();
    //@ close ticket();
    n = n + 1;
    b = random();
  }

  while(0 < n)
    //@ invariant c->x |-> 5 &*& ticket() &*& counter();
  {
    dispose_ticket(c);
    n = n - 1;
  }

  dispose_counter(c);
  free(c);
  
  return 0;
}

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
```

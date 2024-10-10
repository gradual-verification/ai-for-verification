#include "stdlib.h"
// Include VeriFast definitions
//@ #include "nat.gh"

struct C {
    int x;
};

// Predicate declarations
/*@ 
predicate C(struct C *c; int x) = 
    malloc_block_C(c) &*& c->x |-> x;

predicate counter(struct C *c; nat n);

predicate tickets(struct C *c; nat n);
@*/

// We add the verification annotations above the function implementations.
/*@
requires true;
ensures C(result, x);
@*/
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
requires C(c, ?x);
ensures counter(c, zero) &*& C(c, x);
@*/
void create_counter(struct C* c)
{
  //@ close counter(c, zero);
}

/*@
requires counter(c, ?n) &*& n < nat_of_int(INT_MAX) &*& C(c, ?x);
ensures counter(c, succ(n)) &*& C(c, x);
@*/
void create_ticket(struct C* c)
{
  //@ open counter(c, n);
  //@ close counter(c, succ(n));
}

/*@
requires counter(c, succ(?n)) &*& tickets(c, n) &*& C(c, ?x);
ensures counter(c, n) &*& tickets(c, n) &*& C(c, x);
@*/
void dispose_ticket(struct C* c)
{
  //@ open counter(c, succ(n));
  //@ close counter(c, n);
}

/*@
requires counter(c, zero) &*& C(c, ?x);
ensures C(c, x);
@*/
void dispose_counter(struct C* c)
{
  //@ open counter(c, zero);
}

/*@
requires true;
ensures result == true || result == false;
@*/
bool random()
{
  // Assume some Verifast code to retrieve random boolean
  return true;
}

/*@
requires true;
ensures true;
@*/
int main()
{
  struct C* c = create_C(5);
  create_counter(c);
  bool b = random();
  int n = 0;
  while(b && n < INT_MAX) 
  {
    create_ticket(c);
    n = n + 1;
    b = random();
  }

  while(0<n) 
  {
    dispose_ticket(c);
    n = n - 1;
  }
  dispose_counter(c);
  free(c);
  return 0;
}

/*@
requires true;
ensures true;
@*/
int main2()
{
  struct C* c = create_C(3);
  create_counter(c);
  create_ticket(c);
  dispose_ticket(c);
  dispose_counter(c);
  free(c);
  return 0;
}

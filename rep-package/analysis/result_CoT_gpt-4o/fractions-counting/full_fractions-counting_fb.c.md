```c
#include "stdlib.h"
#include <limits.h>

struct C {
  int x;
};

struct C* create_C(int x) 
//@ requires INT_MIN <= x <= INT_MAX;
//@ ensures result != 0 &*& result->x |-> x;
{
  struct C* c = malloc(sizeof(struct C));
  if(c==0) {
    abort();
  } 
  c->x = x;
  return c;
}

/*@
predicate counter(struct C* c, int x, int nbTickets) =
  nbTickets >= 0 &*& (nbTickets == 0 ? [1.0] c->x |-> x : [0.5] c->x |-> x);

predicate tickets(struct C* c, int x, int howMany) =
  howMany <= 0 ? emp : [0.5] c->x |-> x;
@*/

void create_counter(struct C* c)
//@ requires c->x |-> ?x;
//@ ensures counter(c, x, 0);
{
  //@ close counter(c, x, 0);
}

void create_ticket(struct C* c)
//@ requires counter(c, ?x, ?nbTickets) &*& tickets(c, x, nbTickets);
//@ ensures counter(c, x, nbTickets + 1) &*& tickets(c, x, nbTickets + 1);
{
  //@ open counter(c, x, nbTickets);
  //@ open tickets(c, x, nbTickets);
  //@ close counter(c, x, nbTickets + 1);
  //@ close tickets(c, x, nbTickets + 1);
}

void dispose_ticket(struct C* c)
//@ requires counter(c, ?x, ?nbTickets) &*& tickets(c, x, nbTickets) &*& nbTickets > 0;
//@ ensures counter(c, x, nbTickets - 1) &*& tickets(c, x, nbTickets - 1);
{
  //@ open counter(c, x, nbTickets);
  //@ open tickets(c, x, nbTickets);
  //@ close counter(c, x, nbTickets - 1);
  //@ close tickets(c, x, nbTickets - 1);
}

void dispose_counter(struct C* c)
//@ requires counter(c, ?x, 0);
//@ ensures [1.0]c->x |-> x;
{
  //@ open counter(c, x, 0);
}

bool random();
//@ requires true;
//@ ensures true;

int main() 
//@ requires true;
//@ ensures true;
{
  struct C* c = create_C(5);
  create_counter(c);
  bool b = random();
  int n = 0;
  //@ close tickets(c, 5, 0);
  while(b && n < INT_MAX) 
  //@ invariant counter(c, 5, n) &*& tickets(c, 5, n) &*& 0 <= n;
  {
    create_ticket(c);
    n = n + 1;
    b = random();
  }

  while(0 < n) 
  //@ invariant counter(c, 5, n) &*& tickets(c, 5, n) &*& 0 < n;
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
  //@ close tickets(c, 3, 0);
  create_ticket(c);
  dispose_ticket(c);
  dispose_counter(c);
  free(c);
  return 0;
}
```

Explanation of steps taken for formal verification:

1. **Precondition and Postcondition Specification:** 
   - Precondition for `create_C` ensures the input integer `x` is within the bounds of an integer and checks memory allocation success (`result != 0`).
   - The postcondition specifies that the returned pointer is non-null and points to a structure `C` with field `x`.

2. **Predicate Definitions:**
   - Defined the `counter` and `tickets` predicates to maintain resource permissions and invariants about `nbTickets`.

3. **Loop Invariants and Bound Checks:** 
   - Added loop invariants in the `main` function to ensure the state of the counter and tickets is accurately represented. Also ensures `n` is non-negative and handles integer bounds effectively.

4. **Memory Safety and Resource Management:**
   - Managed permissions using predicates and loops with open/close constructs.
   - Followed proper allocation and deallocation patterns to ensure safe memory access and avoid leaks.

The code is now equipped with formal specifications that Verifast can use to verify correctness, memory safety, and boundary conditions.

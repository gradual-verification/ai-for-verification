Below is the modified C code with formal verification in VeriFast, maintaining the original functional behavior:

```c
#include "stdlib.h"
#include "limits.h"

struct C {
  int x;
};

struct C* create_C(int x) 
//@ requires true;
//@ ensures result != 0 &*& result->x |-> x;
{
  struct C* c = malloc(sizeof(struct C));
  if (c == 0) {
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
  //@ open c->x |-> x;
  //@ close counter(c, x, 0);
}

void create_ticket(struct C* c)
//@ requires counter(c, ?x, ?nbTickets) &*& tickets(c, x, nbTickets);
//@ ensures counter(c, x, nbTickets + 1) &*& tickets(c, x, nbTickets + 1);
{
  //@ open counter(c, x, nbTickets);
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
}

void dispose_counter(struct C* c)
//@ requires counter(c, ?x, 0);
//@ ensures [1.0] c->x |-> x;
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
  
  while (b && n < INT_MAX) 
  //@ requires counter(c, 5, n) &*& tickets(c, 5, n);
  //@ ensures counter(c, 5, ?finalN) &*& tickets(c, 5, finalN) &*& finalN >= n;
  {
    //@ open counter(c, 5, n);
    create_ticket(c);
    n = n + 1;
    b = random();
  }
  
  while (0 < n)
  //@ requires counter(c, 5, n) &*& tickets(c, 5, n);
  //@ ensures counter(c, 5, 0) &*& tickets(c, 5, 0);
  {
    //@ open counter(c, 5, n);
    dispose_ticket(c);
    n = n - 1;
  }
  
  dispose_counter(c);
  //@ leak [1.0] c->x |-> 5;
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
  //@ leak [1.0] c->x |-> 3;
  free(c);
  return 0;
}
```

### Explanation:
1. **Preconditions and Postconditions**: The `requires` and `ensures` clauses specify the function preconditions and postconditions, respectively.
2. **Memory Safety**: Checks for non-null pointers, proper allocation, and freeing of memory.
3. **Loop Invariants**: Established by the conditions required to hold before and after each loop iteration, ensuring that they help prove the postconditions and memory safety.
4. **Predicate Use**: Defined predicates to express the state of the object `struct C` in terms of `counter` and `tickets` to track ownership and sharing of memory appropriately.
5. **Resource Management**: Ensures that memory allocated is freed properly and handling of fractional permissions with predicates manages shared and exclusive access to resources correctly.

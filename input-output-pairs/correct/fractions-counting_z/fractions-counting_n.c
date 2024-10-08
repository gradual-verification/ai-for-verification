#include "stdlib.h"

struct C {
  int x;
};

/***
 * Description: 
The create_C function allocates and initializes a new `struct C` object with the given integer value.

@param x - The integer value to initialize the `x` field of the struct.
@return - A pointer to the newly allocated `struct C` object, with its `x` field set to the provided value.

The function ensures that the allocated memory block for the `struct C` object is valid.
If memory allocation fails, the program aborts.
*/
struct C* create_C(int x) 
{
  struct C* c = malloc(sizeof(struct C));
  if(c==0) {
    abort();
  } 
  c->x = x;
  return c;
}

/***
 * Description: 
The create_counter function creates a `counter` predicate for a `struct C` object.

@param c - The given `struct C` object.

In this function, A `counter` predicate created, showing that there is no ticket.
*/
void create_counter(struct C* c)
//@ requires c->x |-> ?x &*& malloc_block_C(c);
//@ ensures counter(c, x, 0);
{
  //@ close counter(c, x, 0);
}

/***
 * Description: 
The create_ticket function creates a new ticket by modifying the `counter` and `tickets` predicate.

@param c - The given `struct C` object.
In this function, the `counter` and `tickets` predicates are updated, showing that the number of tickets is incremented.
*/
void create_ticket(struct C* c)
//@ requires counter(c, ?x, ?nbTickets) &*& tickets(c, x, nbTickets);
//@ ensures counter(c, x, nbTickets + 1) &*& tickets(c, x, nbTickets + 1);
{
  //@ open counter(c, x, nbTickets);
  //@ open tickets(c, x, nbTickets);
  //@ close counter(c, x, nbTickets + 1);
  //@ close tickets(c, x, nbTickets + 1);
}

/***
 * Description: 
The dispose_ticket function disposes a ticket by modifying the `counter` and `tickets` predicate.

@param c - The given `struct C` object, where the `counter` predicate of it satisfies that the number of tickets is bigger than 0.

In this function, the `counter` and `tickets` predicates are updated, showing that the number of tickets is decremented.
*/
void dispose_ticket(struct C* c)
//@ requires counter(c, ?x, ?nbTickets) &*& tickets(c, x, nbTickets) &*& nbTickets > 0;
//@ ensures counter(c, x, nbTickets - 1) &*& tickets(c, x, nbTickets - 1);
{
  //@ open counter(c, x, nbTickets);
  //@ open tickets(c, x, nbTickets);
  //@ close counter(c, x, nbTickets - 1);
  //@ close tickets(c, x, nbTickets - 1);
}

/***
 * Description: 
The dispose_counter function disposes a counter by consuming the `counter` predicate

@param c - The given `struct C` object, where the `counter` predicate of it satisfies that the number of ticket is 0,
which shows that the tickets must be disposed before the counter is disposed.

In this function, the `counter` predicate is consumed and the predicate for `Struct C` is produced.
*/
void dispose_counter(struct C* c)
//@ requires counter(c, ?x, 0);
//@ ensures [1.0]c->x |-> x &*& malloc_block_C(c);
{
  //@ open counter(c, x, 0);
}

/***
 * Description:
The random function generates a random boolean value.

@return A boolean value (`true` or `false`).
The function does not modify the state of any variables, and we don't need to implement it.
*/
bool random();

/***
 * Description:
The main function uses a while loop to test the functions above.

It first creates a C object, then creates a counter and continues creating tickets.
Later, it disposes all tickets and finally dispose the counter and frees the C object.
*/
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

/***
 * Description:
The main function does a simple test on the functions above.

It first creates a C object, then creates a counter and a ticket
Later, it disposes the ticket and the counter ,and finally frees the C object.
*/
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
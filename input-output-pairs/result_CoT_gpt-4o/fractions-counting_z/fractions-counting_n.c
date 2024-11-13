#include "stdlib.h"
#include "stdbool.h"

// Predicate declarations
/*@
predicate struct_C(struct C* c; int x) = 
    c != 0 &*& c->x |-> x;

predicate counter(struct C* c; int tickets) =
    struct_C(c, _) &*& 0 <= tickets;

predicate ticket(struct C* c) =
    counter(c, ?n) &*& n > 0;
@*/

// Function specifications

/***
 * Description: 
 * The create_C function allocates and initializes a new `struct C` object with the given integer value.
 *
 * @param x - The integer value to initialize the `x` field of the struct.
 * @return - A pointer to the newly allocated `struct C` object, with its `x` field set to the provided value.
 *
 * The function ensures that the allocated memory block for the `struct C` object is valid.
 * If memory allocation fails, the program aborts.
 */
/*@
requires true;
ensures struct_C(result, x);
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

/***
 * Description: 
 * The create_counter function creates a `counter` predicate for a `struct C` object.
 *
 * @param c - The given `struct C` object.
 *
 * A `counter` predicate is created, showing that there is no ticket.
 */
/*@
requires struct_C(c, _);
ensures counter(c, 0);
@*/
void create_counter(struct C* c)
{
}

/***
 * Description: 
 * The create_ticket function creates a new ticket by modifying the `counter` and `ticket` predicates.
 *
 * @param c - The given `struct C` object.
 * The `counter` predicate is updated, showing that the number of tickets is incremented.
 */
/*@
requires counter(c, ?n);
ensures counter(c, n + 1);
@*/
void create_ticket(struct C* c)
{
}

/***
 * Description: 
 * The dispose_ticket function disposes a ticket by modifying the `counter` and `ticket` predicates.
 *
 * @param c - The given `struct C` object, where the `counter` predicate of it satisfies that the number of tickets is bigger than 0.
 *
 * The `counter` predicate is updated, showing that the number of tickets is decremented.
 */
/*@
requires counter(c, ?n) &*& n > 0;
ensures counter(c, n - 1);
@*/
void dispose_ticket(struct C* c)
{
}

/***
 * Description: 
 * The dispose_counter function disposes a counter by consuming the `counter` predicate.
 *
 * @param c - The given `struct C` object, where the `counter` predicate of it satisfies that the number of tickets is 0,
 * which shows that the tickets must be disposed before the counter is disposed.
 *
 * The `counter` predicate is consumed and the predicate for `Struct C` is produced.
 */
/*@
requires counter(c, 0);
ensures struct_C(c, _);
@*/
void dispose_counter(struct C* c)
{
}

/***
 * Description:
 * The random function generates a random boolean value.
 *
 * @return A boolean value (`true` or `false`).
 * The function does not modify the state of any variables, and we don't need to implement it.
 */
/*@
requires true;
ensures true;
@*/
bool random();

/***
 * Description:
 * The main function uses a while loop to test the functions above.
 *
 * It first creates a C object, then creates a counter and continues creating tickets.
 * Later, it disposes all tickets and finally disposes the counter and frees the C object.
 */
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
  /*@
  invariant counter(c, n);
  @*/
  {
    create_ticket(c);
    n = n + 1;
    b = random();
  }

  while(0<n) 
  /*@
  invariant counter(c, n);
  @*/
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
 * The main2 function does a simple test on the functions above.
 *
 * It first creates a C object, then creates a counter and a ticket
 * Later, it disposes the ticket and the counter, and finally frees the C object.
 */
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

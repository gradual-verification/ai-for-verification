#include "stdlib.h"
//@ #include "stdlib.gh"

struct Counter {
  int value;
};

//@ predicate counter(struct Counter* c; int v) = malloc_block_Counter(c) &*& c->value |-> v;

/***
 * Description:
 * The init function initializes a new Counter structure with the given initial value.
 * It uses the malloc to allocate the memory for that, if it fails to malloc, the program will terminate.
 *
 * @param v - the initial value in the Counter.
 * @requires - none.
 * @ensures - returns a pointer to a Counter structure with the specified initial value.
 */
struct Counter* init(int v)
  //@ requires true;
  //@ ensures counter(result, v);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  //@ close counter(c, v);
  return c;
}

/***
 * Description:
 * The increment function increments the value of the Counter structure by one.
 *
 * @param c - a pointer to the Counter structure to be incremented.
 * @requires - the Counter structure pointed to by c must be initialized.
 * @ensures - the value of the Counter structure pointed to by c is incremented by one.
 */
void increment(struct Counter* c)
  //@ requires counter(c, ?v);
  //@ ensures counter(c, v + 1);
{
  //@ open counter(c, v);
  c->value = c->value + 1;
  //@ close counter(c, v + 1);
}

/***
 * Description:
 * The dispose function deallocates the memory allocated for the Counter structure.
 *
 * @param c - a pointer to the Counter structure to be deallocated.
 * @requires - the Counter structure pointed to by c must have been initialized.
 * @ensures - the memory allocated for the Counter structure pointed to by c is deallocated.
 */
void dispose(struct Counter* c)
  //@ requires counter(c, _);
  //@ ensures true;
{
  //@ open counter(c, _);
  free(c);
}

/***
 * Description:
 * The swap function swaps the values of two Counter structures.
 *
 * @param c1 - a pointer to the first Counter structure.
 * @param c2 - a pointer to the second Counter structure.
 * @requires - both Counter structures pointed to by c1 and c2 must have been initialized.
 * @ensures - the values of the Counter structures pointed to by c1 and c2 are swapped.
 */
void swap(struct Counter* c1, struct Counter* c2)
  //@ requires counter(c1, ?v1) &*& counter(c2, ?v2);
  //@ ensures counter(c1, v2) &*& counter(c2, v1);
{
  //@ open counter(c1, v1);
  //@ open counter(c2, v2);

  int tmp = c1->value;
  c1->value = c2->value;
  c2->value = tmp;

  //@ close counter(c1, v2);
  //@ close counter(c2, v1);
}

/***
 * Description:
 * The get function retrieves the current value stored in the Counter structure.
 *
 * @param c - a pointer to the Counter structure.
 * @return - the current value stored in the Counter structure.
 * @requires - the Counter structure pointed to by c must have been initialized.
 * @ensures - the current value stored in the Counter structure is returned.
 */
int get(struct Counter* c)
  //@ requires counter(c, ?v);
  //@ ensures counter(c, v) &*& result == v;
{
  //@ open counter(c, v);
  int tmp = c->value;
  //@ close counter(c, v);
  return tmp;
}

/***
 * Description:
 * The main function initializes two Counter structs with initial values, 
 * increments one of them, swaps the values between them, 
 * and then retrieves the value from one of the structs to assert against a known value.
 */
int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct Counter* c1 = init(0);
  struct Counter* c2 = init(5);

  increment(c1);
  swap(c1, c2);
  int tmp = get(c2);

  dispose(c1);
  dispose(c2);
  
  return 0;
}

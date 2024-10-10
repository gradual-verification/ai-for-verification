#include "stdlib.h"
//@ #include "predicates.gh"

struct Counter {
  int value;
};

//@ predicate counter(struct Counter* c, int v) = c->value |-> v;

/*** 
 * Initializes a new Counter structure with the given initial value.
 * @param v the initial value in the Counter struct.
 * @returns the pointer to the newly allocated Counter struct.
 * Ensures the pointer is not null and holds the specified value.
 */
//@ requires true;
//@ ensures result != 0 &*& counter(result, v);
struct Counter* init(int v)
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
 * Increments the value in the Counter struct pointed to by c.
 * @param c the pointer to the Counter struct to be incremented.
 */
//@ requires counter(c, ?v);
//@ ensures counter(c, v + 1);
void increment(struct Counter* c)
{
  //@ open counter(c, _);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close counter(c, tmp + 1);
}

/***
 * Frees the memory allocated for the Counter struct pointed to by c.
 * @param c the pointer to the Counter struct to be disposed of.
 */
//@ requires counter(c, _);
//@ ensures true;
void dispose(struct Counter* c)
{
  //@ open counter(c, _);
  free(c);
}

/*** 
 * Swaps the values stored in the Counter structs pointed to by c1 and c2.
 * @param c1 the pointer to the first Counter struct.
 * @param c2 the pointer to the second Counter struct.
 */
//@ requires counter(c1, ?v1) &*& counter(c2, ?v2);
//@ ensures counter(c1, v2) &*& counter(c2, v1);
void swap(struct Counter* c1, struct Counter* c2)
{
  //@ open counter(c1, _);
  //@ open counter(c2, _);
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  //@ close counter(c1, tmp2);
  //@ close counter(c2, tmp1);
}

/***
 * Retrieves the value stored in the Counter struct pointed to by c.
 * @param c the pointer to the Counter struct to retrieve the value from.
 * @returns the stored value.
 */
//@ requires counter(c, ?v);
//@ ensures counter(c, v) &*& result == v;
int get(struct Counter* c)
{
  //@ open counter(c, v);
  return c->value;
  //@ close counter(c, v);
}

/***
 * Main function execution logic.
 * Initializes two Counter structs, increments one, swaps the values, retrieves a value, and asserts a condition.
 */
//@ requires true;
//@ ensures true;
int main()
{
  struct Counter* c1 = init(0);
  struct Counter* c2 = init(5);

  increment(c1);
  swap(c1, c2);
  int tmp = get(c2);
  assert(tmp == 1);

  dispose(c1);
  dispose(c2);
  return 0;
}

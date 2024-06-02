#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/
/*@
predicate Counter_functional_behavior(struct Counter* c, int v) =
  c->value |-> v;
@*/
struct Counter* init(int v)
//@ requires emp;
  //@ ensures Counter(result, v);

{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;

  //@ close Counter(c, v);
  return c;
}
/**
 * Description:
 * The `increment` function increments the value of the Counter structure by one.
 *
 * @param c A pointer to the Counter structure to be incremented.
 * @requires The Counter structure pointed to by `c` must be initialized.
 * @ensures The value of the Counter structure pointed to by `c` is incremented by one.
 */

void increment(struct Counter* c)
  //@ requires Counter(c, ?v) &*& v < INT_MAX;
  //@ ensures Counter(c, v+1);

{
  //@ open Counter(c, v);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close Counter(c, v+1);
}
/**
 * Description:
 * The `dispose` function deallocates the memory allocated for the Counter structure.
 *
 * @param c A pointer to the Counter structure to be deallocated.
 * @requires The Counter structure pointed to by `c` must have been initialized.
 * @ensures The memory allocated for the Counter structure pointed to by `c` is deallocated.
 */

void dispose(struct Counter* c)
  //@ requires Counter(c, _);
  //@ ensures emp;
{
  //@ open Counter(c, _);
  free(c);
}

/**
 * Description:
 * The `swap` function swaps the values of two Counter structures.
 *
 * @param c1 A pointer to the first Counter structure.
 * @param c2 A pointer to the second Counter structure.
 * @requires Both Counter structures pointed to by `c1` and `c2` must have been initialized.
 * @ensures The values of the Counter structures pointed to by `c1` and `c2` are swapped.
 */

void swap(struct Counter* c1, struct Counter* c2)
  //@ requires Counter(c1, ?v1) &*& Counter(c2, ?v2);
  //@ ensures Counter(c1, v2) &*& Counter(c2, v1); 
{
  //@ open Counter(c1, v1); 
  //@ open Counter(c2, v2);
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  //@ close Counter(c1, v2);
  //@ close Counter(c2, v1);
}
/**
 * Description:
 * The `get` function retrieves the current value stored in the Counter structure.
 *
 * @param c A pointer to the Counter structure.
 * @return The current value stored in the Counter structure.
 * @requires The Counter structure pointed to by `c` must have been initialized.
 * @ensures The current value stored in the Counter structure is returned.
 */
int get(struct Counter* c)
  //@ requires Counter(c, ?v);
  //@ ensures Counter(c, v) &*& result==v; 
{
  //@ open Counter(c, v);
  int tmp = c->value;
  //@ close Counter(c, v);
  return tmp;
}

int main() //@ : main
  //@ requires emp;
  //@ ensures emp;
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = get(c2);
  //@ assert tmp == 1;
  
  dispose(c1); dispose(c2);
  return 0;
}
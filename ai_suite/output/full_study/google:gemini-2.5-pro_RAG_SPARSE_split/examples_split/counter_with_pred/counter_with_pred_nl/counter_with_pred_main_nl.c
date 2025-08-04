#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate counter(struct Counter* c, int v) =
    c->value |-> v &*& malloc_block_Counter(c);
@*/


/***
 * Description:
The init function creates a new counter with the given value.

@param v: the given value to be set

The function makes sure that the returned value is an counter whose value is v.
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

  return c;
}


/***
 * Description:
The increment function increments the value of the counter by 1.

@param c: a pointer to a Counter

The function makes sure that the counter has its value incremented by 1.
*/
void increment(struct Counter* c)
    //@ requires counter(c, ?v);
    //@ ensures counter(c, v + 1);
{
  int tmp = c->value;
  c->value = tmp + 1;
}


/***
 * Description:
The dispose function frees the memory allocated for the Counter.

@param c: a pointer to a Counter

The function makes sure that the counter c is freed.
*/
void dispose(struct Counter* c)
    //@ requires counter(c, _);
    //@ ensures emp;
{
  free(c);
}


/***
 * Description:
The swap function swaps the values of the two Counters.

@param c1, c2: pointers to two Counter

The function makes sure that the two counters have their values swapped.
*/
void swap(struct Counter* c1, struct Counter* c2)
    //@ requires counter(c1, ?v1) &*& counter(c2, ?v2);
    //@ ensures counter(c1, v2) &*& counter(c2, v1);
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}


/***
 * Description:
The get function gets the values of the given counter.

@param c: pointer to a Counter

The function makes sure that the counter c is unchanged and the return value is the value of c.
*/
int get(struct Counter* c)
    //@ requires counter(c, ?v);
    //@ ensures counter(c, v) &*& result == v;
{
  int tmp = c->value;
  return tmp;
}


// TODO: make this function pass the verification
/***
 * Description:
The main function tests the operations of Counter.
*/
int main() //@ : main
{
  struct Counter* c1 = init(0);
  struct Counter* c2 = init(5);

  increment(c1);
  swap(c1, c2);
  int tmp = get(c2);
  //@ assert tmp == 1;

  dispose(c1);
  dispose(c2);
  return 0;
}
#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/
/**
 * Description:
This function initializes a counter object with an initial value.

Specification:

Precondition:
The function is invoked with an integer value v.
There are no additional preconditions.
Postcondition:
Upon completion, the function ensures the creation of a counter object with the specified initial value.
The created counter object satisfies the Counter predicate.
*/
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
/*
Description:
This function increments the value of a counter object by one.

Specification:

Precondition:
The function is invoked with a pointer c to a counter object.
The counter object satisfies the Counter predicate with a value v, where v is less than INT_MAX.
Postcondition:
Upon completion, the function ensures that the counter object's value is incremented by one.
The counter object continues to satisfy the Counter predicate with the new incremented value.*/

void increment(struct Counter* c)
  //@ requires Counter(c, ?v) &*& v < INT_MAX;
  //@ ensures Counter(c, v+1);
{
  //@ open Counter(c, v);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close Counter(c, v+1);
}
/*
Function: void dispose(struct Counter* c)

Description:
This function deallocates the memory associated with a counter object.

Specification:

Precondition:
The function is invoked with a pointer c to a counter object.
The counter object satisfies the Counter predicate.
Postcondition:
Upon completion, the function ensures that all resources associated with the counter object are deallocated.
There are no additional resources or predicates remaining after the execution of the function.*/

void dispose(struct Counter* c)
  //@ requires Counter(c, _);
  //@ ensures emp;
{
  //@ open Counter(c, _);
  free(c);
}

/**
 *

Description:
This function swaps the values of two counter objects.

Specification:

Precondition:
The function is invoked with pointers c1 and c2 to two counter objects.
Both counter objects satisfy the Counter predicate, with values v1 and v2 respectively.
Postcondition:
Upon completion, the function ensures that the values of the counter objects are swapped.
The counter object c1 retains the value originally held by c2, and vice versa.
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
/*
Specification:

Precondition:
The function is invoked with a pointer c to a counter object.
The counter object satisfies the Counter predicate with a value v.
Postcondition:
Upon completion, the function ensures that the counter object retains its original value v.
The function returns the value v of the counter object.*/
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
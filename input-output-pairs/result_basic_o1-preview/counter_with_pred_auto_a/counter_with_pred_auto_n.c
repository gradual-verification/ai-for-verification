#include "stdlib.h"

/*@
predicate Counter_fields(struct Counter* c) =
  c->value |-> _;

predicate counter_uninit(struct Counter *c) =
  malloc_block_Counter(c) &*& Counter_fields(c);

predicate counter(struct Counter *c; int v) =
  c->value |-> v;
@*/

struct Counter {
  int value;
};

/***
 * Description:
The init function initializes a new Counter structure with the given initial value.
It uses malloc to allocate the memory for that, if it fails to malloc, the program will terminate.

@param v - the initial value in the Counter struct.
*/
/*@
requires true;
ensures counter(result, v);
@*/
struct Counter* init(int v)
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  //@ close malloc_block_Counter(c);
  //@ close Counter_fields(c);
  c->value = v;
  //@ close counter(c, v);
  return c;
}

/***
 * Description:
The increment function retrieves the current value from the Counter struct pointed to by c, 
increments it by 1, and updates the value in the struct. 

@param c - the pointer to the Counter struct to be incremented.
*/
/*@
requires counter(c, ?v);
ensures counter(c, v + 1);
@*/
void increment(struct Counter* c)
{
  //@ open counter(c, v);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close counter(c, v + 1);
}

/***
 * Description:
The dispose function frees the memory allocated for the Counter struct pointed to by c.

@param c - the pointer to the Counter struct to be disposed of.
*/
/*@
requires counter(c, _);
ensures true;
@*/
void dispose(struct Counter* c)
{
  //@ open counter(c, _);
  //@ open Counter_fields(c);
  //@ open malloc_block_Counter(c);
  free(c);
}

/*** 
 * Description:
The swap function swaps the values stored in the Counter structs pointed to by c1 and c2.

@param c1 - the pointer to the first Counter struct.
@param c2 - the pointer to the second Counter struct.
*/
/*@
requires counter(c1, ?v1) &*& counter(c2, ?v2);
ensures counter(c1, v2) &*& counter(c2, v1);
@*/
void swap(struct Counter* c1, struct Counter* c2)
{
  //@ open counter(c1, v1);
  int tmp1 = c1->value;
  //@ close counter(c1, v1);
  //@ open counter(c2, v2);
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  //@ close counter(c1, v2);
  //@ close counter(c2, v1);
}

/***
 * Description:
The get function retrieves and returns the value stored in the Counter struct pointed to by c.

@param c - the pointer to the Counter struct to retrieve the value from.
*/
/*@
requires counter(c, ?v);
ensures counter(c, v) &*& result == v;
@*/
int get(struct Counter* c)
{
  //@ open counter(c, v);
  int tmp = c->value;
  //@ close counter(c, v);
  return tmp;
}

/***
 * Description:
The main function initializes two Counter structs with initial values, 
increments one of them, swaps the values between them, 
and then retrieves the value from one of the structs to assert against a known value.
*/
/*@
requires true;
ensures true;
@*/
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

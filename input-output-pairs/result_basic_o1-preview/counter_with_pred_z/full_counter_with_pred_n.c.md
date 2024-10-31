```c
#include "stdlib.h"

/*@
predicate counter(struct Counter* c; int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/

struct Counter {
  int value;
};

/***
 * Description:
The init function initializes a new Counter structure with the given initial value.
It uses the malloc to allocate the memory for that, if it fails to malloc, the program will terminate.

@param v - the initial value in the Counter.
@requires - none.
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
    //@ unreachable;
  }
  //@ c->value |-> _;
  c->value = v;
  //@ close counter(c, v);

  return c;
}

/***
 * Description:
The increment function increments the value of the Counter structure by one.

@param c - a pointer to the Counter structure to be incremented.
@requires - the Counter structure pointed to by c must be initialized.
@ensures - the value of the Counter structure pointed to by c is incremented by one.
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
The dispose function deallocates the memory allocated for the Counter structure.

@param c - a pointer to the Counter structure to be deallocated.
@requires - the Counter structure pointed to by c must have been initialized.
@ensures - the memory allocated for the Counter structure pointed to by c is deallocated.
*/
/*@
requires counter(c, _);
ensures true;
@*/
void dispose(struct Counter* c)
{
  //@ open counter(c, _);
  free(c);
}

/***
 * Description:
The swap function swaps the values of two Counter structures.

@param c1 - a pointer to the first Counter structure.
@param c2 - a pointer to the second Counter structure.
@requires - both Counter structures pointed to by c1 and c2 must have been initialized.
@ensures - the values of the Counter structures pointed to by c1 and c2 are swapped.
*/
/*@
requires counter(c1, ?v1) &*& counter(c2, ?v2);
ensures counter(c1, v2) &*& counter(c2, v1);
@*/
void swap(struct Counter* c1, struct Counter* c2)
{
  //@ open counter(c1, v1);
  //@ open counter(c2, v2);
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  //@ close counter(c1, v2);
  //@ close counter(c2, v1);
}

/***
 * Description:
The get function retrieves the current value stored in the Counter structure.

@param c - a pointer to the Counter structure.
@return - the current value stored in the Counter structure.
@requires - the Counter structure pointed to by c must have been initialized.
@ensures - the current value stored in the Counter structure is returned.
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
int main() //@ : main
{
  struct Counter* c1 = init(0); 
  struct Counter* c2 = init(5);
  //@ assert counter(c1, 0) &*& counter(c2, 5);

  increment(c1); 
  //@ assert counter(c1, 1) &*& counter(c2, 5);

  swap(c1, c2); 
  //@ assert counter(c1, 5) &*& counter(c2, 1);

  int tmp = get(c2);
  //@ assert tmp == 1;

  dispose(c1); 
  dispose(c2);
  return 0;
}
```

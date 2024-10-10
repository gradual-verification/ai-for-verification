```c
#include "stdlib.h"

// Define the structure for a Counter
struct Counter {
  int value;
};

// Define the Verifast predicate for a Counter
/*@
predicate Counter(struct Counter* c, int v) =
  c->value |-> v &*& malloc_block_Counter(c);
@*/

// Function to initialize a Counter with a given value
struct Counter* init(int v)
//@ requires emp;
//@ ensures Counter(result, v);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;

  return c;
}

// Function to increment the value of a Counter
void increment(struct Counter* c)
//@ requires Counter(c, ?v) &*& v < INT_MAX;
//@ ensures Counter(c, v+1);
{
  int tmp = c->value; // Read the current value
  c->value = tmp + 1; // Increment the value
}

// Function to dispose of a Counter, freeing its memory
void dispose(struct Counter* c)
//@ requires Counter(c, _);
//@ ensures emp;
{
  free(c); // Free the allocated memory
}

// Function to swap the values of two Counter structures
void swap(struct Counter* c1, struct Counter* c2)
//@ requires Counter(c1, ?v1) &*& Counter(c2, ?v2);
//@ ensures Counter(c1, v2) &*& Counter(c2, v1); 
{
  int tmp1 = c1->value; // Get the value of c1
  int tmp2 = c2->value; // Get the value of c2
  c2->value = tmp1;     // Assign the value of c1 to c2
  c1->value = tmp2;     // Assign the value of c2 to c1
}

// Function to get the value of a Counter
int get(struct Counter* c)
//@ requires Counter(c, ?v);
//@ ensures Counter(c, v) &*& result==v; 
{
  int tmp = c->value; // Return the current value
  return tmp;
}

// Main function demonstrating the use of Counter
int main() //@ : main
//@ requires emp;
//@ ensures emp;
{
  struct Counter* c1 = init(0); // Initialize c1 with value 0
  struct Counter* c2 = init(5); // Initialize c2 with value 5

  increment(c1); // Increment the value of c1
  swap(c1, c2);  // Swap values of c1 and c2
  int tmp = get(c2); // Get the value of c2 (originally c1's value)

  dispose(c1); // Dispose of c1
  dispose(c2); // Dispose of c2
  return 0;
}
```

In this code, I've included all necessary Verifast annotations to specify preconditions and postconditions for each function. Specifically, it uses the `Counter` predicate to maintain and ensure the consistency of operations on the `Counter` data structure. The specifications cover requirements like memory ownership, correct results from functions, and memory safety guarantees.

To implement formal code verification in VeriFast for the provided C code, we must add preconditions, postconditions, and loop invariants (if there are loops) for each function, ensuring memory safety and correctness of integer operations. Here is the revised code with the required specifications:

```c
#include "stdlib.h"

struct Counter {
  int value;
};

/*@ predicate Counter(struct Counter* c; int v) =
      c->value |-> v &*& malloc_block_Counter(c);
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
  return c;
}

void increment(struct Counter* c)
//@ requires Counter(c, ?v) &*& v < INT_MAX;
//@ ensures Counter(c, v+1);
{
  // Increment the value and ensure it does not overflow
  int tmp = c->value;
  c->value = tmp + 1;
}

void dispose(struct Counter* c)
//@ requires Counter(c, _);
//@ ensures emp;
{
  // Free the allocated memory for the counter
  free(c);
}

void swap(struct Counter* c1, struct Counter* c2)
//@ requires Counter(c1, ?v1) &*& Counter(c2, ?v2);
//@ ensures Counter(c1, v2) &*& Counter(c2, v1);
{
  // Swap the values of two counter objects
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  
  c2->value = tmp1;
  c1->value = tmp2;
}

int get(struct Counter* c)
//@ requires Counter(c, ?v);
//@ ensures Counter(c, v) &*& result == v;
{
  // Return the value of the counter
  return c->value;
}

int main() //@ : main
//@ requires emp;
//@ ensures emp;
{
  // Initialize two counters with different values
  struct Counter* c1 = init(0);
  struct Counter* c2 = init(5);

  // Increment the first counter, swap the values and get the value
  increment(c1);
  swap(c1, c2);
  int tmp = get(c2);
  
  // Verify the value after the swap
  assert(tmp == 1);
  
  // Dispose the counters to free up memory
  dispose(c1);
  dispose(c2);
  
  return 0;
}
```

### Explanation:

- **Precondition and Postcondition**: Each function has preconditions and postconditions. They specify the state of memory and integer bounds before and after the function executes, ensuring memory safety and correctness of operations. The predicates ensure conditions like correct memory allocation (`malloc_block_Counter`) and access permission to the counter's state (`c->value |-> v`).

- **Memory Safety**: Precondition ensures memory block ownership of the counter is correct, while postcondition ensures the memory block is either still correctly managed (increased reference) or freed properly when no longer needed.

- **Integer Bounds**: The function `increment` checks for overflow prevention (`v < INT_MAX`).

- **Main Function**: Calls validate through the verification tool ensuring counter initialization, modification, and cleanup steps adhere to pre/postconditions, maintaining the program's correctness and safety throughout its execution.

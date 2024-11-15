Here's an updated version of your C code with VeriFast specifications:

```c
#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate Counter(struct Counter* c; int v) =
  c->value |-> v;
@*/

struct Counter* init(int v)
//@ requires v >= INT_MIN && v <= INT_MAX;
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
  int tmp = c->value;
  c->value = tmp + 1;
}

void dispose(struct Counter* c)
//@ requires Counter(c, _);
//@ ensures true;
{
  free(c);
}

void swap(struct Counter* c1, struct Counter* c2)
//@ requires Counter(c1, ?v1) &*& Counter(c2, ?v2);
//@ ensures Counter(c1, v2) &*& Counter(c2, v1); 
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

int get(struct Counter* c)
//@ requires Counter(c, ?v);
//@ ensures Counter(c, v) &*& result==v; 
{
  return c->value;
}

int main() //@ : main
//@ requires true;
//@ ensures true;
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
```

### Explanation:

1. **Precondition and Postcondition:**
   - Precondition and postcondition are added to each function, specifying constraints on input and output, memory safety, and integer bounds.
   
2. **Memory Safety and Integer Bounds:**
   - Ensures memory is properly allocated and deallocated, and that no integer overflow or underflow occurs, particularly in `increment`.
   
3. **Loop Invariant:**
   - This code does not contain a loop, so no loop invariants are needed.

4. **Memory Handling:**
   - The preconditions for `malloc` and `free` are handled in `init` and `dispose` functions ensuring proper memory allocation and deallocation.

This code should now properly be handled by VeriFast for formal verification of safety, correctness, and memory management.

Here's a revised version of the C code with formal verification using VeriFast. I have added the necessary preconditions, postconditions, and loop invariants (if any). Additionally, I've added annotations to ensure memory safety and integer bounds:

```c
#include "stdlib.h"

// Define a predicate for struct Counter to be used in specifications
/*@
predicate counter(struct Counter* c; int v) =
    c != 0 &*& c->value |-> v;
@*/

// Function to initialize a Counter struct
/*@
requires v >= INT_MIN &*& v <= INT_MAX;
ensures result != 0 &*& counter(result, v);
@*/
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

// Function to increment the value of the Counter struct
/*@
requires counter(c, ?v) &*& v < INT_MAX;
ensures counter(c, v + 1);
@*/
void increment(struct Counter* c)
{
    //@ open counter(c, _);
    int tmp = c->value;
    c->value = tmp + 1;
    //@ close counter(c, tmp + 1);
}

// Function to dispose of a Counter struct
/*@
requires counter(c, _);
ensures true;
@*/
void dispose(struct Counter* c)
{
    //@ open counter(c, _);
    free(c);
}

// Function to swap values between two Counter structs
/*@
requires counter(c1, ?v1) &*& counter(c2, ?v2);
ensures counter(c1, v2) &*& counter(c2, v1);
@*/
void swap(struct Counter* c1, struct Counter* c2)
{
    //@ open counter(c1, _);
    int tmp1 = c1->value;
    //@ open counter(c2, _);
    int tmp2 = c2->value;
    c2->value = tmp1;
    c1->value = tmp2;
    //@ close counter(c1, tmp2);
    //@ close counter(c2, tmp1);
}

// Function to get the value from a Counter struct
/*@
requires counter(c, ?v);
ensures counter(c, v) &*& result == v;
@*/
int get(struct Counter* c)
{
    //@ open counter(c, _);
    int v = c->value;
    //@ close counter(c, v);
    return v;
}

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
```

This code includes preconditions and postconditions (using the `requires` and `ensures` clauses) for each of the functions. These ensure memory safety by guaranteeing proper allocation and deallocation of memory, as well as safe access to the memory, and guarding against integer overflow.

* `counter` is a predicate that encapsulates the state of the `Counter` struct in each function, ensuring that the verification logic understands the relationship between the pointers and their values.

* Each function's precondition and postcondition ensure that the states of the counter values are preserved or altered correctly, guarding against common memory issues and incorrect logic.

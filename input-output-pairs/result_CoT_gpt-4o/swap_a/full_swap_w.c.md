```c
#include "stdlib.h"
#include <stdbool.h>

// Predicate definitions for memory safety checks
//@ predicate int_ptr(int *p, int value) = *p |-> value;
//@ predicate struct_point_pred(struct point* p, int x, int y) = p != 0 &*& p->x |-> x &*& p->y |-> y;

void swap(int *a, int *b)
//@ requires int_ptr(a, ?x) &*& int_ptr(b, ?y);
//@ ensures int_ptr(a, y) &*& int_ptr(b, x);
{
    // Open predicate to access memory
    //@ open int_ptr(a, x);
    //@ open int_ptr(b, y);
    int tmp = *a;
    *a = *b;
    *b = tmp;
    // Close predicate after memory operation
    //@ close int_ptr(a, y);
    //@ close int_ptr(b, x);
}

struct point {
    int x;
    int y;
};

void point_mirror(struct point *p)
//@ requires struct_point_pred(p, ?x, ?y);
//@ ensures struct_point_pred(p, y, x);
{
    // Open the struct_point_pred to access fields
    //@ open struct_point_pred(p, x, y);
    swap(&p->x, &p->y);
    // Close the struct_point_pred with swapped values
    //@ close struct_point_pred(p, y, x);
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    
    // Initialize the point and create a predicate for it
    p->x = 3;
    p->y = 10;
    //@ close struct_point_pred(p, 3, 10);
    
    point_mirror(p);
    
    // Open the predicate to check the values
    //@ open struct_point_pred(p, 10, 3);
    bool b = p->x == 10 && p->y == 3;
    assert(b);

    // Clean up memory
    //@ close struct_point_pred(p, 10, 3); // Re-close before deallocation
    free(p);
    return 0;
}
```

Here, I've added detailed preconditions, postconditions, and predicate definitions to ensure correct functional behavior and memory safety. The predicates `int_ptr` and `struct_point_pred` ensure that the memory pointed by `int*` and `struct point*` are accounted for. The open and close statements manage the lifecycle of these predicates across the function calls and variable access points to align with Verifast's usage requirements.

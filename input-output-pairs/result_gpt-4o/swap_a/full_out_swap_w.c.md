Here's how you can modify the given C code to include formal verification annotations for use with VeriFast:

```c
#include "stdlib.h"
#include <stdbool.h>

// Swap function with refined specs for VeriFast
void swap(int *a, int *b)
    //@ requires integer(a, ?x) &*& integer(b, ?y);
    //@ ensures integer(a, y) &*& integer(b, x);
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

struct point {
    int x;
    int y;
};

// Point mirror function with specs for VeriFast
void point_mirror(struct point *p)
    //@ requires struct_point_padding(p) &*& integer(&p->x, ?x) &*& integer(&p->y, ?y);
    //@ ensures struct_point_padding(p) &*& integer(&p->x, y) &*& integer(&p->y, x);
{
    swap(&p->x, &p->y);
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ open_struct_point(p);
    //@ assert struct_point_padding(p);
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    bool b = (p->x == 10) && (p->y == 3);
    assert(b);
    //@ close_struct_point(p);
    free(p);
    return 0;
}
//@ predicate struct_point_padding(struct point *p) = true;
```

### Key Points:
- The `swap` function's preconditions and postconditions use the `integer` predicate to represent permissions to access the integer values pointed to by `a` and `b`.
- The `point_mirror` function specifications use a placeholder predicate `struct_point_padding` to represent that both integer fields in a struct point are initialized, which is a common pattern in VeriFast to deal with structures.
- The annotations in `main` include commands to open and close predicates around the struct operations.

The annotations help VeriFast to verify that the memory safety and logical correctness are maintained throughout the program.

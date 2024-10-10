```c
#include "stdlib.h"
#include <stdbool.h>

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

void point_mirror(struct point *p)
//@ requires p->x |-> ?x &*& p->y |-> ?y;
//@ ensures p->x |-> y &*& p->y |-> x;
{
    //@ open p->x |-> x &*& p->y |-> y;
    swap(&p->x, &p->y);
    //@ close p->x |-> y &*& p->y |-> x;
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ close p->x |-> 3 &*& p->y |-> 10;
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    //@ open p->x |-> 10 &*& p->y |-> 3;
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    free(p);
    return 0;
}
```

In the verification specification, `integer(a, ?x)` denotes that `a` is a pointer to an integer holding the value `x`, and `?x` is a ghost variable that represents the pre-condition value. The `|->` field predicates are used to describe the ownership of structure fields.

To use Verifast effectively, you must always pair ownership predicates (like field pointers) with `open` and `close` statements to specify when you're revealing and claiming the resource described by the predicate. This helps Verifast track the access permissions and ensures that the program adheres to the specified constraints. The function `swap()` has specification contracts for `requires` (preconditions) and `ensures` (postconditions) to guarantee correct swapping behavior. 

Note also the use of `abort()` in `main()` to handle the case where `malloc` returns `NULL`, which is a good practice to ensure that the memory allocation is guaranteed successful before performing operations on it with Verifast.

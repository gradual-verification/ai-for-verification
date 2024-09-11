#include "stdlib.h"

//@ predicate foo(int x; int y);
//@ predicate bar(int x; int y) = foo(x, y);

void foo()
    //@ requires foo(10, 100);
    //@ ensures foo(10, 100);
{
    
}
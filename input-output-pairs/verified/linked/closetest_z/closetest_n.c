#include "stdlib.h"

//@ predicate foo(int x; int y);
//@ predicate bar(int x; int y) = foo(x, y);

/***
 * Description:
The foo function aims at testing the renaming of predicate and the opening and closing of predicate.
So its code is empty and doesn't have functional behavior.

@param none
*/
void foo()
{
    //@ close bar(10, ?y);
    //@ open bar(10, y);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
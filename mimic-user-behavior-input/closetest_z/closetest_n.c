#include "stdlib.h"

/*
  Natural Language Specification:

  1. Includes and Predicates
     - The program includes the standard library header file (stdlib.h).
     - Two predicates are defined:
       - foo(int x; int y): A predicate named foo that takes two integer arguments x and y.
       - bar(int x; int y): A predicate named bar that is defined to be equivalent to the predicate foo(x, y).

  2. Function Definition
     - A function named foo is defined with no parameters.

  3. Function Requirements and Ensures
     - Preconditions:
       - Before the function is called, a specific predicate condition involving integers is required to be true.
     - Postconditions:
       - After the function is executed, the same specific predicate condition involving integers must be true.

  4. Function Body
     - Within the function body:
       - The function asserts a predicate using an existential quantifier.
       - The function then deconstructs the previously asserted predicate to expose a specific value.
*/


//@ predicate foo(int x; int y);
//@ predicate bar(int x; int y) = foo(x, y);

void foo()
    //@ requires foo(10, 100);
    //@ ensures foo(10, 100);
{
    //@ close bar(10, ?y);
    //@ open bar(10, y);
}
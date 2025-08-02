#include <stdlib.h>
#include <stdio.h>
#include "prelude.h"

//@ #include "prelude_core.gh"
//@ #include "list.gh"

//@ predicate integer(int *p; int v) = int_(p, some(v));

/*@
predicate integer(int *p; int v) =
    int_(p, some(v));
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `inc` function increments the value stored at the memory location 
 * pointed to by `i`.
 *
 * @param i - A pointer to an integer variable that should be incremented.
 *
 * The function makes sure that the value at i is incremented by 1.
 */
void inc(int* i)
    //@ requires integer(i, ?v);
    //@ ensures integer(i, v + 1);
{
    //@ open integer(i, v);
    (*i) = (*i) + 1;
    //@ close integer(i, v + 1);
}
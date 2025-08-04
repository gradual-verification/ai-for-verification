#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate list(struct node *l; list<int> values) =
    l == 0 ?
        values == nil
    :
        l->next |-> ?next &*&
        l->value |-> ?val &*&
        malloc_block_node(l) &*&
        list(next, ?tail) &*&
        values == cons(val, tail);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The break_test function tests whether the break statement can get out of the while loop,
and it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function

It makes sure that n1 and n2 are unchanged. 
*/
void break_test(struct node *n1, struct node *n2)
    //@ requires list(n1, ?vs1) &*& list(n2, ?vs2);
    //@ ensures list(n1, vs1) &*& list(n2, vs2);
{
    while (true)
        //@ invariant list(n1, vs1) &*& list(n2, vs2);
    {
        break;
    }
}
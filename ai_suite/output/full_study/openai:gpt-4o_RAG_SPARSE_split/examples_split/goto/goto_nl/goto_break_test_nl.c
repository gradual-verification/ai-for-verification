#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate node(struct node *n; struct node *next, int value) =
    n != 0 &*& n->next |-> next &*& n->value |-> value;

predicate nodes(struct node *n; list<struct node *> ns) =
    n == 0 ? ns == nil : node(n, ?next, ?value) &*& nodes(next, ?ns0) &*& ns == cons(n, ns0);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The break_test function tests whether the break statement can get out of the while loop,
and it doesn't modify the given parameters.

@param n1, n2: nodes unchanged in this function

It makes sure that n1 and n2 are unchanged. 
*/
/*@
requires nodes(n1, ?ns1) &*& nodes(n2, ?ns2);
ensures nodes(n1, ns1) &*& nodes(n2, ns2);
@*/
void break_test(struct node *n1, struct node *n2)
{
    while (true)
    {
        break;
    }
}
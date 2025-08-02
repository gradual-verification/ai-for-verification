#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@

predicate nodes(struct node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& nodes(next, ?values0) &*& values == cons(value, values0);

@*/

// TODO: make this function pass the verification
int list_length(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    while (node != 0)
    //@ invariant nodes(node, ?values0) &*& i == length(values) - length(values0);
    {
        //@ open nodes(node, values0);
        node = node->next;
        i++;
    }
    //@ open nodes(node, _);
    return i;
}
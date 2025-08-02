#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@
// Define a predicate for a linked list of nodes
predicate nodes(struct node *n; list<int> values) =
    n == 0 ?
        values == nil
    :
        n->next |-> ?next &*& n->value |-> ?value &*& malloc_block_node(n) &*&
        nodes(next, ?values0) &*& values == cons(value, values0);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The dispose_nodes function iteratively frees the nodes of a given linked list, by using a loop with a goto.

@param head: pointing to the head of the given linked list

It makes sure that the nodes in the linked list are freed. 
*/
void dispose_nodes(struct node *head)
//@ requires nodes(head, ?values);
//@ ensures true;
{
loop:
    //@ invariant nodes(head, ?vs);
    if (head == 0) return;
    //@ open nodes(head, vs);
    struct node *next = head->next;
    free(head);
    head = next;
    goto loop;
}
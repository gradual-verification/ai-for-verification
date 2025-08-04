#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
predicate node(struct node *p; struct node *l, struct node *r, struct node *pa, int c) =
    p->left |-> l &*&
    p->right |-> r &*&
    p->parent |-> pa &*&
    p->count |-> c &*&
    malloc_block_node(p);
@*/

// TODO: make this function pass the verification
/*`tree_has_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a left child

It makes sure that the tree is not changed. */
bool tree_has_left(struct node *node)
    //@ requires node == 0 ? true : [?f]node(node, ?l, ?r, ?p, ?c);
    //@ ensures (node == 0 ? true : [f]node(node, l, r, p, c)) &*& result == (node != 0 && l != 0);
{
    bool result = false;
    if (node == 0) {
    } else {
        //@ open [f]node(node, l, r, p, c);
        struct node *left = node->left;
        result = left != 0;
        //@ close [f]node(node, l, r, p, c);
    }
    return result;
}
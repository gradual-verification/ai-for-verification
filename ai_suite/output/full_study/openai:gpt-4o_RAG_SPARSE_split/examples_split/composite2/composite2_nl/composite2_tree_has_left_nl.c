#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    n == 0 ?
        left == 0 &*& right == 0 &*& parent == 0 &*& count == 0
    :
        n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count &*&
        malloc_block_node(n);

@*/

// TODO: make this function pass the verification
/*`tree_has_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a left child

It makes sure that the tree is not changed. */
bool tree_has_left(struct node *node)
    //@ requires node(node, ?left, ?right, ?parent, ?count);
    //@ ensures node(node, left, right, parent, count) &*& result == (left != 0);
{
    bool result = false;
    if (node == 0) {
        //@ open node(node, left, right, parent, count);
        //@ close node(node, left, right, parent, count);
    } else {
        //@ open node(node, left, right, parent, count);
        struct node *left = node->left;
        result = left != 0;
        //@ close node(node, left, right, parent, count);
    }
    return result;
}
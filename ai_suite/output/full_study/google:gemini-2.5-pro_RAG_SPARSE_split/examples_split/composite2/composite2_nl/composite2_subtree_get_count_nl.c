#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
predicate subtree(struct node *n, struct node *p, int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> c &*&
        malloc_block_node(n) &*&
        subtree(l, n, ?lc) &*&
        subtree(r, n, ?rc) &*&
        c == 1 + lc + rc;
@*/

// TODO: make this function pass the verification
/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?p, ?c);
    //@ ensures subtree(node, p, c) &*& result == c;
{
    int result = 0;
    //@ open subtree(node, p, c);
    if (node == 0) {
        // If node is null, from the predicate we know c is 0.
        // result is already 0, so the postcondition will hold.
    } else {
        // If node is not null, we have access to its fields.
        // The predicate ensures node->count is c.
        result = node->count;
    }
    //@ close subtree(node, p, c);
    return result;
}
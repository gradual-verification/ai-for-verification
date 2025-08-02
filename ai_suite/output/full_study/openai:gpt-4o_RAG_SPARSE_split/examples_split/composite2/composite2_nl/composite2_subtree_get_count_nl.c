#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n; int count) =
    n == 0 ?
        count == 0
    :
        n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &*& n->count |-> count &*&
        malloc_block_node(n) &*&
        node(left, ?leftCount) &*& node(right, ?rightCount) &*&
        count == 1 + leftCount + rightCount;

@*/

// TODO: make this function pass the verification
/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires node(node, ?count);
    //@ ensures node(node, count) &*& result == count;
{
    int result = 0;
    if (node == 0) {
        result = 0;
    } else {
        //@ open node(node, count);
        result = node->count;
        //@ close node(node, count);
    }
    return result;
}
#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Predicate to describe a tree with parent pointers and a size-cache field 'count'.
// - n: pointer to the root of the subtree.
// - p: pointer to the parent of n.
// - c: the number of nodes in the subtree rooted at n (output parameter).
predicate subtree(struct node *n, struct node *p; int c) =
    n == 0 ?
        // An empty subtree has 0 nodes.
        c == 0
    :
        // A non-empty subtree consists of the root node...
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> c &*&
        malloc_block_node(n) &*&
        // ...and its left and right subtrees.
        subtree(l, n, ?cl) &*&
        subtree(r, n, ?cr) &*&
        // The count of this subtree is 1 (for the root) + counts of children.
        c == 1 + cl + cr;
@*/


// TODO: make this function pass the verification
/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?p, ?c);
    //@ ensures subtree(node, p, c) &*& result == c;
{
    //@ open subtree(node, p, c);
    int result = 0;
    if (node == 0) {
        // If the node is null, the predicate ensures c is 0.
        // 'result' is already 0, so the postcondition 'result == c' holds.
    } else {
        // If the node is not null, the predicate gives us 'node->count |-> c'.
        // We read this value into 'result'.
        result = node->count;
    }
    //@ close subtree(node, p, c);
    return result;
}
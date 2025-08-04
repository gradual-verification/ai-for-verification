#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// A recursive predicate to represent a valid subtree.
// 'n' is the root of the subtree.
// 'p' is the expected parent of the node 'n'.
// 'count' is an output parameter representing the number of nodes in the subtree.
predicate subtree(struct node *n, struct node *p; int count) =
    n == 0 ?
        // An empty subtree has 0 nodes.
        count == 0
    :
        // A non-empty subtree has a root node 'n' with its fields pointing
        // to its children, parent, and its own count.
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> ?c &*&
        malloc_block_node(n) &*&
        // The left and right children are valid subtrees with 'n' as their parent.
        subtree(l, n, ?lc) &*&
        subtree(r, n, ?rc) &*&
        // The count of the current node must be 1 (for itself) plus the counts
        // of its left and right subtrees.
        c == 1 + lc + rc &*&
        // The total count of the subtree is the count of the root node.
        count == c;

// A predicate for a full tree, which is a subtree whose root has no parent.
predicate tree(struct node *t; int count) = subtree(t, 0, count);
@*/


/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?p, ?c);
    //@ ensures subtree(node, p, c) &*& result == c;
{
    //@ open subtree(node, p, c);
    int result = 0;
    if (node == 0) {
        // If the node is null, the count is 0, as per the predicate.
    } else {
        // If the node is not null, its count field holds the subtree size.
        result = node->count;
    }
    //@ close subtree(node, p, c);
    return result;
}


// TODO: make this function pass the verification
/*`tree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function is used to get the 
count value of the tree starting from the given node.

This function makes sure that the tree of node is not changed. */
int tree_get_count(struct node *node)
    //@ requires tree(node, ?c);
    //@ ensures tree(node, c) &*& result == c;
{
    //@ open tree(node, c);
    int result = subtree_get_count(node);
    //@ close tree(node, c);
    return result;
}
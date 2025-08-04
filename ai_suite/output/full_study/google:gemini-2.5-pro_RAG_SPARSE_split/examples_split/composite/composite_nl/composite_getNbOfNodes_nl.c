#include "stdlib.h"

/*@
// A predicate representing a valid tree node and its subtree.
// 'n' is the node pointer.
// 'p' is the parent of the node 'n'.
// 'size' is the number of nodes in the subtree rooted at 'n'.
predicate Node_pred(struct Node* n, struct Node* p, int size) =
    n == 0 ?
        size == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> size &*&
        malloc_block_Node(n) &*&
        Node_pred(l, n, ?lsize) &*&
        Node_pred(r, n, ?rsize) &*&
        size == 1 + lsize + rsize;
@*/

/***
 * Description:
 * This program implements a tree structure where each node has pointers to 
 * a left child, a right child, and a parent. Nodes store a `count` representing
 * the number of nodes in the subtree.
 *
 * The tree supports:
 * - Creating a root node.
 * - Adding a left child to a node.
 * - Retrieving the number of nodes in a subtree.
 * - Updating node counts recursively.
 */

/***
 * Structure representing a node in the tree.
 * Each node has a left child, a right child, a parent, and an integer count.
 */
struct Node {
    struct Node* left;
    struct Node* right;
    struct Node* parent;
    int count;
};


/***
 * Description:
 * The `internalGetNbOfNodes` function returns the number of nodes in the subtree rooted at `n`.
 *
 * @param n - A pointer to the root node.
 *
 * The function simply returns the `count` field of the node.
 */
int internalGetNbOfNodes(struct Node* n)
    //@ requires Node_pred(n, ?p, ?size) &*& n != 0;
    //@ ensures Node_pred(n, p, size) &*& result == size;
{
    //@ open Node_pred(n, p, size);
    int c = n->count;
    //@ close Node_pred(n, p, size);
    return c;
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `getNbOfNodes` function retrieves the number of nodes in the subtree rooted at `n`.
 *
 * @param n - A pointer to the root of the subtree.
 *
 * The function makes sure not to change the subtree and return the `count` field of the node.
 */
int getNbOfNodes(struct Node* n)
    //@ requires Node_pred(n, ?p, ?size) &*& n != 0;
    //@ ensures Node_pred(n, p, size) &*& result == size;
{
    int c = internalGetNbOfNodes(n);
    return c;
}
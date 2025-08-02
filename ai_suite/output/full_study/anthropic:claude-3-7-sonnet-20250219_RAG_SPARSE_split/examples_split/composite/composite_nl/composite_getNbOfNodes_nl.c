#include "stdlib.h"

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

/*@
// Predicate to represent a valid node in the tree
predicate node(struct Node* n; int nodeCount) =
    n == 0 ?
        nodeCount == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> ?p &*&
        n->count |-> nodeCount &*&
        malloc_block_Node(n) &*&
        node(l, ?lCount) &*&
        node(r, ?rCount) &*&
        nodeCount == 1 + lCount + rCount;
@*/

/***
 * Description:
 * The `internalGetNbOfNodes` function returns the number of nodes in the subtree rooted at `n`.
 *
 * @param n - A pointer to the root node.
 *
 * The function simply returns the `count` field of the node.
 */
int internalGetNbOfNodes(struct Node* n)
//@ requires n != 0 &*& n->count |-> ?c;
//@ ensures n->count |-> c &*& result == c;
{
    int c = n->count;
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
//@ requires node(n, ?count);
//@ ensures node(n, count) &*& result == count;
{
    //@ open node(n, count);
    if (n == 0) {
        //@ close node(n, count);
        return 0;
    } else {
        int c = internalGetNbOfNodes(n);
        //@ close node(n, count);
        return c;
    }
}
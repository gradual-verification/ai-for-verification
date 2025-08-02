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
predicate node(struct Node *n; int depth) =
    n != 0 &*&
    n->left |-> ?left &*&
    n->right |-> ?right &*&
    n->parent |-> ?parent &*&
    n->count |-> ?count &*&
    malloc_block_Node(n) &*&
    count >= 0 &*& count <= INT_MAX - 1;

// Predicate to represent a chain of parent nodes
predicate parent_chain(struct Node *n; int depth) =
    n == 0 ?
        depth == 0
    :
        node(n, _) &*&
        parent_chain(n->parent, depth - 1) &*&
        depth > 0;
@*/

/***
 * Description:
 * The `fix` function updates the `count` field of a non-null node and propagates the update to its ancestors.
 *
 * @param node - A pointer to the node whose count should be updated.
 *
 * The function makes sure that the count field of current node with its ancestors is incremented by 1
 */
void fix(struct Node* node)
//@ requires node(node, ?depth) &*& parent_chain(node->parent, ?pdepth);
//@ ensures node(node, depth) &*& parent_chain(node->parent, pdepth);
{
    int tmp = node->count;
    if (tmp == INT_MAX) {
        abort();
    }
    node->count = tmp + 1;

    struct Node* parent = node->parent;
    if(parent != 0) {
        //@ open parent_chain(parent, pdepth);
        fix(parent);
        //@ close parent_chain(parent, pdepth);
    }
}
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
// Predicate for owning a single Node's fields.
predicate Node_(struct Node *node; struct Node *left, struct Node *right, struct Node *parent, int count) =
    node->left |-> left &*&
    node->right |-> right &*&
    node->parent |-> parent &*&
    node->count |-> count &*&
    malloc_block_Node(node);

// Predicate representing the chain of ancestors from 'node' up to the root.
// This is the state required by the 'fix' function.
// 'counts' is a ghost parameter that stores the initial count values of the nodes on the path.
predicate ancestor_path(struct Node *node; list<int> counts) =
    node != 0 &*&
    Node_(node, ?l, ?r, ?p, ?c) &*&
    c < INT_MAX &*&
    (p == 0 ?
        counts == cons(c, nil)
    :
        ancestor_path(p, ?p_counts) &*&
        counts == cons(c, p_counts)
    );

// Predicate representing the state of the ancestor chain after 'fix' has been called.
// Each node's count has been incremented by 1.
// 'old_counts' is the list of counts from before the fix.
predicate ancestor_path_fixed(struct Node *node; list<int> old_counts) =
    node != 0 &*&
    Node_(node, ?l, ?r, ?p, head(old_counts) + 1) &*&
    (p == 0 ?
        tail(old_counts) == nil
    :
        ancestor_path_fixed(p, tail(old_counts))
    );
@*/


// TODO: make this function pass the verification
/***
 * Description:
 * The `fix` function updates the `count` field of a non-null node and propagates the update to its ancestors.
 *
 * @param node - A pointer to the node whose count should be updated.
 *
 * The function makes sure that the count field of current node with its ancestors is incremented by 1
 */
void fix(struct Node* node)
    //@ requires ancestor_path(node, ?old_counts);
    //@ ensures ancestor_path_fixed(node, old_counts);
{
    //@ open ancestor_path(node, old_counts);
    //@ open Node_(node, ?l, ?r, ?p, ?c);
    
    int tmp = node->count;
    if (tmp == INT_MAX) {
        abort();
    }
    node->count = tmp + 1;

    struct Node* parent = node->parent;
    if(parent != 0) {
        fix(parent);
    }
    
    //@ close Node_(node, l, r, p, c + 1);
    //@ close ancestor_path_fixed(node, old_counts);
}
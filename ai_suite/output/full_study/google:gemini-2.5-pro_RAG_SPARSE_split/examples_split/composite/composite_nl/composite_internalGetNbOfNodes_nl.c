/*@
// A predicate to describe a valid tree structure.
// 'n' is the root of the tree, 'p' is its parent.
// 'size' is an output parameter representing the number of nodes in the tree.
// This is a "precise" predicate (indicated by the semicolon ';'), meaning
// the output 'size' is uniquely determined by the inputs 'n' and 'p'.
predicate is_tree(struct Node *n, struct Node *p; int size) =
    n == 0 ?
        // An empty tree has size 0.
        size == 0
    :
        // A non-empty tree has a root node 'n'.
        // We must own the memory for the node and its fields.
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> ?c &*&
        malloc_block_Node(n) &*&
        // The left and right children must be valid trees with 'n' as their parent.
        is_tree(l, n, ?lsize) &*&
        is_tree(r, n, ?rsize) &*&
        // The total size is 1 (for the root) + sizes of subtrees.
        size == 1 + lsize + rsize &*&
        // The 'count' field must store the correct size of the subtree.
        c == size;
@*/
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
// A predicate to describe a valid tree structure.
// 'n' is the root of the tree, 'p' is its parent.
// 'size' is an output parameter representing the number of nodes in the tree.
// This is a "precise" predicate (indicated by the semicolon ';'), meaning
// the output 'size' is uniquely determined by the inputs 'n' and 'p'.
predicate is_tree(struct Node *n, struct Node *p; int size) =
    n == 0 ?
        // An empty tree has size 0.
        size == 0
    :
        // A non-empty tree has a root node 'n'.
        // We must own the memory for the node and its fields.
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> ?c &*&
        malloc_block_Node(n) &*&
        // The left and right children must be valid trees with 'n' as their parent.
        is_tree(l, n, ?lsize) &*&
        is_tree(r, n, ?rsize) &*&
        // The total size is 1 (for the root) + sizes of subtrees.
        size == 1 + lsize + rsize &*&
        // The 'count' field must store the correct size of the subtree.
        c == size;
@*/


// TODO: make this function pass the verification
/***
 * Description:
 * The `internalGetNbOfNodes` function returns the number of nodes in the subtree rooted at `n`.
 *
 * @param n - A pointer to the root node.
 *
 * The function simply returns the `count` field of the node.
 */
int internalGetNbOfNodes(struct Node* n)
    //@ requires n != 0 &*& is_tree(n, ?p, ?size);
    //@ ensures n != 0 &*& is_tree(n, p, size) &*& result == size;
{
    // Open the predicate to access the fields of the node 'n'.
    // This makes the chunks for n->left, n->right, n->parent, and n->count available.
    //@ open is_tree(n, p, size);
    
    // Read the count from the node.
    int c = n->count;
    
    // Close the predicate to restore the invariant.
    // Since we only read from the node, the state is unchanged, and we can close it.
    //@ close is_tree(n, p, size);
    
    // The 'c' variable holds the value of n->count, which is equal to 'size'.
    return c;
}
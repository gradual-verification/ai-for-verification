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
// Predicate for a single node's memory layout.
predicate Node(struct Node *n; struct Node *left, struct Node *right, struct Node *parent, int count) =
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    malloc_block_Node(n);

// Predicate for a valid tree structure.
// 'n' is the root of the subtree, 'p' is its parent, and 'c' is the node count.
predicate tree(struct Node *n; struct Node *p, int c) =
    n == 0 ?
        c == 0
    :
        Node(n, ?l, ?r, p, c) &*&
        tree(l, n, ?lc) &*&
        tree(r, n, ?rc) &*&
        c == 1 + lc + rc;
@*/


/***
 * Description:
 * The `create` function creates and returns a new tree node with no children.
 *
 * @returns A pointer to a newly allocated `Node`.
 *
 * This function makes sure to return a tree with one node. 
 */
struct Node* create() 
    //@ requires true;
    //@ ensures tree(result, 0, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->parent = 0;
    n->left = 0;
    n->right = 0;
    n->count = 1;
    
    //@ close tree(0, n, 0);
    //@ close tree(0, n, 0);
    //@ close tree(n, 0, 1);
  
    return n;
}


// TODO: make this function pass the verification
/***
 * Description:
 * The `internalCreate` function creates a new node with a given parent.
 *
 * @param parent - A pointer to the parent node.
 *
 * The function makes sure that the returned node is not null and a subtree with that node is linked to the parent.
 */
struct Node* internalCreate(struct Node* parent)
    //@ requires true;
    //@ ensures tree(result, parent, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = parent;
    n->count = 1;

    //@ close tree(0, n, 0);
    //@ close tree(0, n, 0);
    //@ close tree(n, parent, 1);

    return n;
}
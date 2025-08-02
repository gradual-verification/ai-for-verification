#include "stdlib.h"
#include "limits.h"

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
predicate node(struct Node* n, struct Node* parent, int count) =
    n->parent |-> parent &*& n->left |-> ?left &*& n->right |-> ?right &*& n->count |-> count &*&
    malloc_block_Node(n) &*&
    (left == 0 ? true : node(left, n, ?leftCount)) &*&
    (right == 0 ? true : node(right, n, ?rightCount)) &*&
    count == 1 + (left == 0 ? 0 : leftCount) + (right == 0 ? 0 : rightCount);

predicate tree(struct Node* root) =
    root == 0 ? true : node(root, 0, ?count);
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
    //@ ensures node(result, 0, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->parent = 0;
    n->left = 0;
    n->right = 0;
    n->count = 1;
    //@ close node(n, 0, 1);
    return n;
}

/***
 * Description:
 * The `internalCreate` function creates a new node with a given parent.
 *
 * @param parent - A pointer to the parent node.
 *
 * The function makes sure that the returned node is not null and a subtree with that node is linked to the parent.
 */
struct Node* internalCreate(struct Node* parent)
    //@ requires node(parent, ?grandparent, ?parentCount);
    //@ ensures node(parent, grandparent, parentCount) &*& node(result, parent, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = parent;
    n->count = 1;
    //@ close node(n, parent, 1);
    return n;
}

/***
 * Description:
 * The `internalAddLeft` function creates and adds a left child to a node.
 *
 * @param node - A pointer to the node where the left child should be added. The node has empty left child.
 *
 * The function makes sure to add a left child to node and updates the `count` field of its ancestors by incrementing by 1.
 */
struct Node* internalAddLeft(struct Node* node)
    //@ requires node(node, ?parent, ?count) &*& node->left |-> 0;
    //@ ensures node(node, parent, count + 1);
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}

/***
 * Description:
 * The `fix` function updates the `count` field of a non-null node and propagates the update to its ancestors.
 *
 * @param node - A pointer to the node whose count should be updated.
 *
 * The function makes sure that the count field of current node with its ancestors is incremented by 1
 */
void fix(struct Node* node)
    //@ requires node(node, ?parent, ?count);
    //@ ensures node(node, parent, count + 1);
{
    int tmp = node->count;
    if (tmp == INT_MAX) {
        abort();
    }
    node->count = tmp + 1;

    struct Node* parent = node->parent;
    if(parent != 0) {
        fix(parent);
    }
    //@ close node(node, parent, count + 1);
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `addLeft` function adds a left child to a given node and returns the newly added child.
 *
 * @param node - A pointer to the node where the left child should be added, and its both children are originally empty.
 *
 * The function makes sure that a new (and distinct) left child node is added and returned.
 */
struct Node* addLeft(struct Node* node)
    //@ requires node(node, ?parent, ?count) &*& node->left |-> 0;
    //@ ensures node(node, parent, count + 1) &*& node(result, node, 1);
{
    struct Node* newChild = internalAddLeft(node);
    return newChild;
}
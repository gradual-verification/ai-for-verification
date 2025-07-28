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


/***
 * Description:
 * The `internalCreate` function creates a new node with a given parent.
 *
 * @param parent - A pointer to the parent node.
 *
 * The function makes sure that the returned node is not null and a subtree with that node is linked to the parent.
 */
struct Node* internalCreate(struct Node* parent)
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = parent;
    n->count = 1;

    return n;
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
}


// TODO: make this function pass the verification
/***
 * Description:
 * The `internalAddLeft` function creates and adds a left child to a node.
 *
 * @param node - A pointer to the node where the left child should be added. The node has empty left child.
 *
 * The function makes sure to add a left child to node and updates the `count` field of its ancestors by incrementing by 1.
 */
struct Node* internalAddLeft(struct Node* node)
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}


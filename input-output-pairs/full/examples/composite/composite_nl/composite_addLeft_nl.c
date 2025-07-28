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
{
    struct Node* newChild = internalAddLeft(node);
    return newChild;
}


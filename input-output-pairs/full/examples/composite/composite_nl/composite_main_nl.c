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


/***
 * Description:
 * The `getNbOfNodes` function retrieves the number of nodes in the subtree rooted at `n`.
 *
 * @param n - A pointer to the root of the subtree.
 *
 * The function makes sure not to change the subtree and return the `count` field of the node.
 */
int getNbOfNodes(struct Node* n)
{
    int c = internalGetNbOfNodes(n);
    return c;
}


/***
 * Description:
 * The `create` function creates and returns a new tree node with no children.
 *
 * @returns A pointer to a newly allocated `Node`.
 *
 * This function makes sure to return a tree with one node. 
 */
struct Node* create() 
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->parent = 0;
    n->left = 0;
    n->right = 0;
    n->count = 1;
  
    return n;
}


// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function demonstrates tree operations by:
 * - Creating a root node.
 * - Adding a left child.
 * - Adding another left child to the previous one.
 * - Retrieving and asserting the number of nodes in the subtree.
 */
int main() 
{
    struct Node* mytree = create();
    struct Node* child = addLeft(mytree);
    struct Node* child2 = addLeft(child);
  
    int c = getNbOfNodes(child2);
    assert(c == 1);
    abort();
}


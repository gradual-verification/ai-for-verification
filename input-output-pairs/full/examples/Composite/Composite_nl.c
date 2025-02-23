#include <stdbool.h>
#include <limits.h>
#include <stdlib.h>
#include <assert.h>

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

/***
 * Description:
 * The `create` function creates and returns a new tree node with no children.
 *
 * @returns A pointer to a newly allocated `Node`.
 *
 * The function allocates memory for a new node, initializes its fields (`left`, `right`, `parent` to `NULL`), 
 * sets `count` to 1, and returns it.
 * If memory allocation fails, the program aborts.
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

/***
 * Description:
 * The `addLeft` function adds a left child to a given node and returns the newly added child
 *
 * @param node - A pointer to the node where the left child should be added.
 *
 * The function calls `internalAddLeft(node)`, which allocates and initializes
 * a new left child node and updates the tree structure.
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
 * The function calls `internalGetNbOfNodes(n)`, which reads and returns the `count` field of the node.
 */
int getNbOfNodes(struct Node* n)
{
    int c = internalGetNbOfNodes(n);
    return c;
}

/***
 * Description:
 * The `internalCreate` function creates a new node with a given parent.
 *
 * @param parent - A pointer to the parent node.
 *
 * The function allocates memory for a new node, initializes its fields (`left` and `right` to `NULL`),
 * sets its parent pointer, and initializes `count` to 1.
 * If memory allocation fails, the program aborts.
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
 * The `internalAddLeft` function creates and adds a left child to a node.
 *
 * @param node - A pointer to the node where the left child should be added.
 *
 * The function calls `internalCreate(node)` to create a new node, assigns it as the left child,
 * and updates the `count` field by calling `fix(node)`.
 */
struct Node* internalAddLeft(struct Node* node)
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}

/***
 * Description:
 * The `fix` function updates the `count` field of a node and propagates the update to its ancestors.
 *
 * @param node - A pointer to the node whose count should be updated.
 *
 * The function increments the `count` field by 1, ensuring it does not exceed `INT_MAX`.
 * It then recursively updates the parent node, if it exists.
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

/***
 * Description:
 * The `abort` function enters an infinite loop, simulating a program termination state.
 *
 * This function is used when an unrecoverable error occurs.
 */
void abort()
{
    while(true) 
    {
    }
}

/***
 * Description:
 * The `internalGetNbOfNodes` function returns the number of nodes in the subtree rooted at `n`.
 *
 * @param n - A pointer to the root node.
 *
 * The function simply returns the `count` field of the node.
 */
int internalGetNbOfNodes(struct Node* n)
{
    int c = n->count;
    return c;
}

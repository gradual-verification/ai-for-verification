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
predicate nodes(struct Node* node, struct Node* parent, int count) =
    node == 0 ? count == 0 : 
    node->parent |-> parent &*& node->left |-> ?left &*& node->right |-> ?right &*& node->count |-> count &*&
    malloc_block_Node(node) &*&
    nodes(left, node, ?leftCount) &*& nodes(right, node, ?rightCount) &*& count == 1 + leftCount + rightCount;
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
    //@ ensures nodes(result, 0, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->parent = 0;
    n->left = 0;
    n->right = 0;
    n->count = 1;
    //@ close nodes(n, 0, 1);
    return n;
}

/***
 * Description:
 * The `addLeft` function adds a left child to a given node and returns the newly added child.
 *
 * @param node - A pointer to the node where the left child should be added, and its both children are originally empty.
 *
 * The function makes sure that a new (and distinct) left child node is added and returned.
 */
struct Node* addLeft(struct Node* node)
    //@ requires nodes(node, ?parent, ?count) &*& node->left |-> 0;
    //@ ensures nodes(node, parent, count + 1) &*& result != 0 &*& nodes(result, node, 1);
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
    //@ requires nodes(n, ?parent, ?count);
    //@ ensures nodes(n, parent, count) &*& result == count;
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
 * The function makes sure that the returned node is not null and a subtree with that node is linked to the parent.
 */
struct Node* internalCreate(struct Node* parent)
    //@ requires nodes(parent, ?grandparent, ?parentCount);
    //@ ensures nodes(parent, grandparent, parentCount + 1) &*& nodes(result, parent, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = parent;
    n->count = 1;
    //@ close nodes(n, parent, 1);
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
    //@ requires nodes(node, ?parent, ?count) &*& node->left |-> 0;
    //@ ensures nodes(node, parent, count + 1) &*& result != 0 &*& nodes(result, node, 1);
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
    //@ requires nodes(node, ?parent, ?count);
    //@ ensures nodes(node, parent, count + 1);
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
 * The `internalGetNbOfNodes` function returns the number of nodes in the subtree rooted at `n`.
 *
 * @param n - A pointer to the root node.
 *
 * The function simply returns the `count` field of the node.
 */
int internalGetNbOfNodes(struct Node* n)
    //@ requires nodes(n, ?parent, ?count);
    //@ ensures nodes(n, parent, count) &*& result == count;
{
    int c = n->count;
    return c;
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
    //@ requires true;
    //@ ensures true;
{
    struct Node* mytree = create();
    struct Node* child = addLeft(mytree);
    struct Node* child2 = addLeft(child);
  
    int c = getNbOfNodes(child2);
    //@ assert c == 1;
    abort();
}
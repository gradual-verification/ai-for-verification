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
// Define a predicate for a tree node
predicate tree(struct Node *n; int count) =
    n == 0 ?
        count == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> ?p &*&
        n->count |-> count &*&
        malloc_block_Node(n) &*&
        tree(l, ?lcount) &*&
        tree(r, ?rcount) &*&
        count == 1 + lcount + rcount;
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
//@ ensures tree(result, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->parent = 0;
    n->left = 0;
    n->right = 0;
    n->count = 1;
    
    //@ close tree(0, 0);
    //@ close tree(0, 0);
    //@ close tree(n, 1);
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
//@ requires tree(node, ?count) &*& node != 0;
//@ ensures tree(node, count + 1) &*& tree(result, 1) &*& result != 0 &*& result->parent |-> node;
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
//@ requires tree(n, ?count);
//@ ensures tree(n, count) &*& result == count;
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
//@ requires true;
//@ ensures result != 0 &*& result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> parent &*& result->count |-> 1 &*& malloc_block_Node(result);
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
 * @param node - A pointer to the node where the left child should be added. The node has empty left child.
 *
 * The function makes sure to add a left child to node and updates the `count` field of its ancestors by incrementing by 1.
 */
struct Node* internalAddLeft(struct Node* node)
//@ requires node != 0 &*& node->left |-> 0 &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?count &*& malloc_block_Node(node) &*& tree(r, ?rcount);
//@ ensures node != 0 &*& node->left |-> result &*& node->right |-> r &*& node->parent |-> p &*& node->count |-> count + 1 &*& malloc_block_Node(node) &*& tree(r, rcount) &*& result != 0 &*& result->parent |-> node &*& tree(result, 1);
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    
    //@ close tree(0, 0);
    //@ close tree(0, 0);
    //@ close tree(child, 1);
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
//@ requires node != 0 &*& node->count |-> ?count &*& count < INT_MAX;
//@ ensures node != 0 &*& node->count |-> count + 1;
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
//@ requires n == 0 ? true : n->count |-> ?count;
//@ ensures n == 0 ? result == 0 : n->count |-> count &*& result == count;
{
    int c = n == 0 ? 0 : n->count;
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
    //@ assert tree(mytree, 1);
    
    struct Node* child = addLeft(mytree);
    //@ assert tree(mytree, 2);
    //@ assert tree(child, 1);
    
    struct Node* child2 = addLeft(child);
    //@ assert tree(child, 2);
    //@ assert tree(child2, 1);
  
    int c = getNbOfNodes(child2);
    assert(c == 1);
    
    // Free all allocated memory to avoid leaks
    //@ open tree(child2, 1);
    free(child2);
    //@ open tree(child, 2);
    free(child);
    //@ open tree(mytree, 2);
    free(mytree);
    
    return 0;
}
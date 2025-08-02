#include "stdlib.h"
#include "limits.h"

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
predicate node(struct Node* n; struct Node* left, struct Node* right, struct Node* parent, int count) =
    n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count &*& malloc_block_Node(n);

predicate tree(struct Node* root, struct Node* parent; int count) =
    root == 0 ?
        count == 0
    :
        node(root, ?left, ?right, parent, count) &*&
        tree(left, root, ?leftCount) &*&
        tree(right, root, ?rightCount) &*&
        count == leftCount + rightCount + 1;
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
    //@ close node(n, 0, 0, 0, 1);
    //@ close tree(n, 0, 1);
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
    //@ requires node(parent, ?left, ?right, ?p, ?count);
    //@ ensures node(parent, left, right, p, count) &*& tree(result, parent, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = parent;
    n->count = 1;
    //@ close node(n, 0, 0, parent, 1);
    //@ close tree(n, parent, 1);
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
    //@ requires node(node, ?left, ?right, ?parent, ?count) &*& count < INT_MAX;
    //@ ensures node(node, left, right, parent, count + 1);
{
    int tmp = node->count;
    if (tmp == INT_MAX) {
        abort();
    }
    node->count = tmp + 1;

    struct Node* parent = node->parent;
    if(parent != 0) {
        //@ open node(parent, ?l, ?r, ?p, ?pc);
        fix(parent);
        //@ close node(parent, l, r, p, pc + 1);
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
    //@ requires node(node, 0, ?right, ?parent, ?count) &*& count < INT_MAX;
    //@ ensures node(node, result, right, parent, count + 1) &*& tree(result, node, 1);
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}
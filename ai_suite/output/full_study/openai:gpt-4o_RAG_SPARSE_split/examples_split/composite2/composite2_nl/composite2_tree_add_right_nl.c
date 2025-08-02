#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count &*& malloc_block_node(n);

predicate tree(struct node *n) =
    n == 0 ? true : node(n, ?left, ?right, ?parent, ?count) &*& tree(left) &*& tree(right);

@*/

/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires node(node, ?left, ?right, ?parent, ?count);
    //@ ensures node(node, left, right, parent, count) &*& result == count;
{
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    return result;
}

/*`fixup_ancestors()` Function:
- Parameters: Takes a node pointer, parent pointer, 
and the new count as input.
- Description: This function updates the count of the
  ancestors of the provided node based on the new count
  provided.
  
It makes sure that the node's count is updated with the given value and the ancestors' count is also updated. */
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires node(node, ?left, ?right, parent, ?nodeCount) &*& node(parent, ?pLeft, ?pRight, ?pParent, ?pCount) &*& tree(pLeft) &*& tree(pRight);
    //@ ensures node(node, left, right, parent, count) &*& node(parent, pLeft, pRight, pParent, ?newPCount) &*& tree(pLeft) &*& tree(pRight);
{
    if (parent == 0) {
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else if (node == right && node != left) {
            leftCount = subtree_get_count(left);
            rightCount = count;
        } else {
            abort();
        }
        // to avoid integer overflow
        if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort(); }
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        fixup_ancestors(parent, grandparent, parentCount);
    }
}

// TODO: make this function pass the verification
/*`tree_add_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: It adds a new node as the right child 
of the input node by following a similar process 
of memory allocation, setting pointers, and 
updating count values. 

It makes sure to return the new node in the tree. */
struct node *tree_add_right(struct node *node)
    //@ requires node(node, ?left, 0, ?parent, ?count) &*& tree(left);
    //@ ensures node(node, left, result, parent, ?newCount) &*& node(result, 0, 0, node, 1) &*& tree(left);
{
    if (node == 0) {
        abort();
    }
    {
        struct node *n = malloc(sizeof(struct node));
        if (n == 0) {
            abort();
        }
        n->left = 0;
        n->right = 0;
        n->parent = node;
        n->count = 1;
        {
            struct node *nodeRight = node->right;
            if (nodeRight != 0) {
                abort();
            }
            node->right = n;
            if (n == node->left) {
                abort();
            }
            fixup_ancestors(n, node, 1);
        }
        return n;
    }
}
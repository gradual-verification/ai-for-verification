#include "stdlib.h"
#include "limits.h"

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

/* subtree_get_count function
   -param: struct node *node
   -description: The function gets the count of the current node,
   which is the number of nodes in the subtree rooted at the node.

   It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
int subtree_get_count(struct node *node)
    //@ requires node(node, ?left, ?right, ?parent, ?count) &*& tree(left) &*& tree(right);
    //@ ensures node(node, left, right, parent, count) &*& tree(left) &*& tree(right) &*& result == count;
{
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    return result;
}

// TODO: make this function pass the verification
/* fixup_ancestors function
   -param: struct node *node, struct node *parent, int count
   -description: The function fixes the count of the ancestors
   of the current node. Here, parameter `count` is the number of nodes
   in the subtree rooted at node.

   It makes sure that the counts of the node and ancestors are updated correctly.
*/
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires node(node, ?left, ?right, parent, count) &*& tree(left) &*& tree(right) &*& node(parent, ?pleft, ?pright, ?pparent, ?pcount) &*& tree(pleft) &*& tree(pright);
    //@ ensures node(node, left, right, parent, count) &*& tree(left) &*& tree(right) &*& node(parent, pleft, pright, pparent, ?new_pcount) &*& tree(pleft) &*& tree(pright);
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
        {
            if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort(); }
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            fixup_ancestors(parent, grandparent, parentCount);
        }
    }
}
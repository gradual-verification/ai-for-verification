#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a node in the tree
predicate node_with_count(struct node *n, int count) =
    n == 0 ?
        count == 0
    :
        n->left |-> ?left &*&
        n->right |-> ?right &*&
        n->parent |-> ?parent &*&
        n->count |-> count &*&
        malloc_block_node(n) &*&
        count == 1 + subtree_count(left) + subtree_count(right);

// Define a fixpoint function to calculate the count of a subtree
fixpoint int subtree_count(struct node *n) {
    return n == 0 ? 0 : 1 + subtree_count(n->left) + subtree_count(n->right);
}

// Define a predicate for a node and its ancestors
predicate node_and_ancestors(struct node *n, struct node *parent) =
    n == 0 ?
        true
    :
        node_with_count(n, ?count) &*&
        (parent == 0 ? true : node_and_ancestors(parent, parent->parent));
@*/

/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
int subtree_get_count(struct node *node)
//@ requires node == 0 ? true : [?f]node->count |-> ?count;
//@ ensures node == 0 ? result == 0 : [f]node->count |-> count &*& result == count;
{
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    return result;
}

/*fixup_ancestors function
-param: struct node *node, struct node *parent, int count
-description: The function fixes the count of the ancestors
of the current node. Here, parameter `count` is the number of nodes
in the subtree rooted at node.

It makes sure that the counts of the node and ancestors are updated correctly.
*/
void fixup_ancestors(struct node *node, struct node *parent, int count)
//@ requires node != 0 &*& node_with_count(node, _) &*& (parent == 0 ? true : node_and_ancestors(parent, parent->parent)) &*& count >= 0;
//@ ensures node_with_count(node, count) &*& (parent == 0 ? true : node_and_ancestors(parent, parent->parent));
{
    if (parent == 0) {
        //@ close node_with_count(node, count);
    } else {
        //@ open node_and_ancestors(parent, parent->parent);
        //@ open node_with_count(parent, _);
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
            if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort();}
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            fixup_ancestors(parent, grandparent, parentCount);
            //@ close node_with_count(parent, parentCount);
            //@ close node_and_ancestors(parent, parent->parent);
        }
    }
}
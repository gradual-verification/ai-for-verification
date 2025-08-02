#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Predicate for a binary tree node
predicate tree_node(struct node *node, int count) =
    node != 0 &*&
    node->left |-> ?left &*&
    node->right |-> ?right &*&
    node->parent |-> ?parent &*&
    node->count |-> count &*&
    malloc_block_node(node) &*&
    count > 0;

// Predicate for a subtree
predicate subtree(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        tree_node(node, count);
@*/

/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
//@ requires subtree(node, ?count);
//@ ensures subtree(node, count) &*& result == count;
int subtree_get_count(struct node *node)
{
    int result = 0;
    if (node == 0) {
        //@ close subtree(node, 0);
    } else {
        //@ open subtree(node, count);
        result = node->count;
        //@ close tree_node(node, count);
        //@ close subtree(node, count);
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
//@ requires node != 0 &*& tree_node(node, count) &*& parent != 0 &*& tree_node(parent, ?parent_count);
//@ ensures tree_node(node, count) &*& tree_node(parent, _);
void fixup_ancestors(struct node *node, struct node *parent, int count)
{
    if (parent == 0) {
        //@ close tree_node(node, count);
    } else {
        //@ open tree_node(parent, parent_count);
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
            if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            //@ close tree_node(node, count);
            if (grandparent != 0) {
                //@ open subtree(grandparent, _);
                fixup_ancestors(parent, grandparent, parentCount);
            } else {
                //@ close tree_node(parent, parentCount);
            }
        }
    }
}


// TODO: make this function pass the verification
/*tree_add_right function
-param: struct node *node
-description: The function adds a right node to the
current node. It requires that before the call, the current node is non-null and its right node is null.
It returns the newly added node and makes sure that it is the right child of the given node.
*/
//@ requires node != 0 &*& tree_node(node, ?count) &*& node->right |-> 0;
//@ ensures tree_node(node, _) &*& tree_node(result, 1) &*& result->parent |-> node;
struct node *tree_add_right(struct node *node)
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
        //@ open tree_node(node, count);
        struct node *nodeRight = node->right;
        node->right = n;
        //@ close tree_node(n, 1);
        fixup_ancestors(n, node, 1);
    }
    return n;
}
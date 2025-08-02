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
    count == 1 + subtree_count(left) + subtree_count(right);

// Fixpoint function to calculate the count of a subtree
fixpoint int subtree_count(struct node *node) {
    return node == 0 ? 0 : 1 + subtree_count(node->left) + subtree_count(node->right);
}

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
int subtree_get_count(struct node *node)
//@ requires subtree(node, ?count);
//@ ensures subtree(node, count) &*& result == count;
{
    int result = 0;
    if (node == 0) {
        //@ close subtree(node, 0);
    } else {
        //@ open tree_node(node, count);
        result = node->count;
        //@ close tree_node(node, count);
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
//@ requires node != 0 &*& parent != 0 &*& parent->left |-> ?left &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?old_count &*& malloc_block_node(parent) &*& (node == left || node == right) &*& node != left || node != right;
//@ ensures parent->left |-> left &*& parent->right |-> right &*& parent->parent |-> grandparent &*& parent->count |-> ?new_count &*& malloc_block_node(parent) &*& new_count == 1 + (node == left ? count : subtree_count(left)) + (node == right ? count : subtree_count(right));
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
            //@ open subtree(right, rightCount);
            //@ close subtree(right, rightCount);
        } else if (node == right && node != left) {
            leftCount = subtree_get_count(left);
            //@ open subtree(left, leftCount);
            //@ close subtree(left, leftCount);
            rightCount = count;
        } else {
            abort();
        }
        {
            if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            fixup_ancestors(parent, grandparent, parentCount);
        }
    }
}


// TODO: make this function pass the verification
/*tree_add_left function
-param: struct node *node
-description: The function adds a left node to the
current node. It requires that before the call, the current node is non-null and its left node is null.
It returns the newly added node and makes sure that it is the left child of the given node.
*/
struct node *tree_add_left(struct node *node)
//@ requires tree_node(node, ?count) &*& node->left |-> 0;
//@ ensures tree_node(node, count + 1) &*& tree_node(result, 1) &*& result->parent |-> node &*& node->left |-> result;
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
        struct node *nodeLeft = node->left;
        node->left = n;
        //@ close tree_node(n, 1);
        fixup_ancestors(n, node, 1);
        //@ close tree_node(node, count + 1);
    }
    return n;
}
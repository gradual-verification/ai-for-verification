#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate tree(struct node *node, struct node *parent, int count) =
    node == 0 ?
        count == 0
    :
        node->parent |-> parent &*& node->count |-> count &*&
        node->left |-> ?left &*& node->right |-> ?right &*&
        malloc_block_node(node) &*&
        tree(left, node, ?leftCount) &*&
        tree(right, node, ?rightCount) &*&
        count == 1 + leftCount + rightCount;

@*/

/*create_tree function
-param: void
-description: The function creates a tree with one node and returns it.

It makes sure that the returned value is a tree with one node.
*/
struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, 0, 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close tree(n, 0, 1);
    return n;
}

/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
int subtree_get_count(struct node *node)
    //@ requires tree(node, ?parent, ?count);
    //@ ensures tree(node, parent, count) &*& result == count;
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
    //@ requires tree(node, parent, count) &*& tree(parent, ?grandparent, ?parentCount);
    //@ ensures tree(node, parent, count) &*& tree(parent, grandparent, 1 + subtree_get_count(parent->left) + subtree_get_count(parent->right));
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

/*tree_add_left function
-param: struct node *node
-description: The function adds a left node to the
current node. It requires that before the call, the current node is non-null and its left node is null.
It returns the newly added node and makes sure that it is the left child of the given node.
*/
struct node *tree_add_left(struct node *node)
    //@ requires tree(node, ?parent, ?count) &*& node->left |-> 0;
    //@ ensures tree(result, node, 1) &*& tree(node, parent, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    //@ open tree(node, parent, count);
    node->left = n;
    fixup_ancestors(n, node, 1);
    //@ close tree(n, node, 1);
    //@ close tree(node, parent, count + 1);
    return n;
}

/*tree_add_right function
-param: struct node *node
-description: The function adds a right node to the
current node. It requires that before the call, the current node is non-null and its right node is null.
It returns the newly added node and makes sure that it is the right child of the given node.
*/
struct node *tree_add_right(struct node *node)
    //@ requires tree(node, ?parent, ?count) &*& node->right |-> 0;
    //@ ensures tree(result, node, 1) &*& tree(node, parent, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    //@ open tree(node, parent, count);
    node->right = n;
    fixup_ancestors(n, node, 1);
    //@ close tree(n, node, 1);
    //@ close tree(node, parent, count + 1);
    return n;
}

/*tree_get_parent function
-param: struct node *node
-description: The function gets the parent of the
current node. It requires that before the call, the current node and its parent are non-null.
It makes sure that the returned value is the parent of the current node and the tree is not changed.
*/
struct node *tree_get_parent(struct node *node)
    //@ requires tree(node, ?parent, ?count) &*& parent != 0;
    //@ ensures tree(node, parent, count) &*& result == parent;
{
    struct node *parent = node->parent;
    return parent;
}

/*dispose_node function
-param: struct node *node
-description: The function disposes the tree by calling
itself recursively on the left and right nodes of the
current node. It then frees the current node.

It makes sure that the subtree of node is freed.
*/
void dispose_node(struct node *node)
    //@ requires tree(node, ?parent, _);
    //@ ensures true;
{
    if (node == 0) {
    } else {
        //@ open tree(node, parent, _);
        {
            struct node *left = node->left;
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        free(node);
    }
}

/*tree_dispose function
-param: struct node *node
-description: The function disposes the tree by calling 
the dispose_node function.

It makes sure that the tree of node is freed.
*/
void tree_dispose(struct node *node)
    //@ requires tree(node, 0, _);
    //@ ensures true;
{
    dispose_node(node);
}

// TODO: make this function pass the verification
/*main function
-param: void
-description: The function creates a tree and adds 
left and right nodes to the tree. It then gets the 
parent of the right node and adds a left node to it.
It then gets the parent of the left node and disposes 
the tree.
*/
int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *node0 = create_tree();
    struct node *node = node0;
    node = tree_add_left(node);
    node = tree_add_right(node);
    node = tree_get_parent(node);
    node = tree_add_left(node);
    node = tree_get_parent(node);
    node = tree_get_parent(node);
    tree_dispose(node);
    return 0;
}
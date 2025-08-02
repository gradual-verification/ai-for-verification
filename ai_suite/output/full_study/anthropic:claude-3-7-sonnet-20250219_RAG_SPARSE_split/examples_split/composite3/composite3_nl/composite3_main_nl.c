#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a tree node
predicate tree_node(struct node *n, int count) =
    n != 0 ?
        n->left |-> ?left &*&
        n->right |-> ?right &*&
        n->parent |-> ?parent &*&
        n->count |-> count &*&
        malloc_block_node(n) &*&
        ((left == 0 ? true : tree_node(left, ?leftCount) &*& left->parent |-> n) &*&
         (right == 0 ? true : tree_node(right, ?rightCount) &*& right->parent |-> n) &*&
         count == 1 + (left == 0 ? 0 : leftCount) + (right == 0 ? 0 : rightCount))
    :
        true;

// Define a lemma to help with tree node disposal
lemma void tree_node_dispose(struct node *n)
    requires tree_node(n, ?count);
    ensures true;
{
    if (n != 0) {
        open tree_node(n, count);
        if (n->left != 0) {
            tree_node_dispose(n->left);
        }
        if (n->right != 0) {
            tree_node_dispose(n->right);
        }
    }
}
@*/

/*create_tree function
-param: void
-description: The function creates a tree with one node and returns it.

It makes sure that the returned value is a tree with one node.
*/
struct node *create_tree()
//@ requires true;
//@ ensures tree_node(result, 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close tree_node(result, 1);
    return n;
}


/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
int subtree_get_count(struct node *node)
//@ requires node == 0 ? true : [?f]tree_node(node, ?count);
//@ ensures node == 0 ? result == 0 : [f]tree_node(node, count) &*& result == count;
{
    int result = 0;
    if (node == 0) {
    } else {
        //@ open [f]tree_node(node, count);
        result = node->count;
        //@ close [f]tree_node(node, count);
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
//@ requires node != 0 &*& parent != 0 &*& tree_node(node, count) &*& tree_node(parent, ?parentCount) &*& (parent->left == node || parent->right == node) &*& node->parent == parent;
//@ ensures tree_node(node, count) &*& tree_node(parent, ?newParentCount);
{
    if (parent == 0) {
    } else {
        //@ open tree_node(parent, parentCount);
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            leftCount = count;
            //@ if (right != 0) { open tree_node(right, _); close tree_node(right, _); }
            rightCount = subtree_get_count(right);
        } else if (node == right && node != left) {
            //@ if (left != 0) { open tree_node(left, _); close tree_node(left, _); }
            leftCount = subtree_get_count(left);
            rightCount = count;
        } else {
            abort();
        }
        {
            if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort();}
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            //@ close tree_node(parent, parentCount);
            if (grandparent != 0) {
                //@ open tree_node(parent, parentCount);
                //@ close tree_node(parent, parentCount);
                fixup_ancestors(parent, grandparent, parentCount);
            }
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
//@ requires tree_node(node, ?count) &*& node != 0 &*& node->left |-> 0;
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
    }
    return n;
}


/*tree_add_right function
-param: struct node *node
-description: The function adds a right node to the
current node. It requires that before the call, the current node is non-null and its right node is null.
It returns the newly added node and makes sure that it is the right child of the given node.
*/
struct node *tree_add_right(struct node *node)
//@ requires tree_node(node, ?count) &*& node != 0 &*& node->right |-> 0;
//@ ensures tree_node(node, count + 1) &*& tree_node(result, 1) &*& result->parent |-> node &*& node->right |-> result;
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


/*tree_get_parent function
-param: struct node *node
-description: The function gets the parent of the
current node. It requires that before the call, the current node and its parent are non-null.
It makes sure that the returned value is the parent of the current node and the tree is not changed.
*/
struct node *tree_get_parent(struct node *node)
//@ requires [?f]tree_node(node, ?count) &*& node != 0 &*& [f]node->parent |-> ?parent &*& parent != 0;
//@ ensures [f]tree_node(node, count) &*& result == parent;
{
    //@ open [f]tree_node(node, count);
    struct node *parent = node->parent;
    //@ close [f]tree_node(node, count);
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
//@ requires tree_node(node, ?count);
//@ ensures true;
{
    if (node == 0) {
    } else {
        //@ open tree_node(node, count);
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

It makes sure that the tree of noed is freed.
*/
void tree_dispose(struct node *node)
//@ requires tree_node(node, ?count);
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
    
    //@ open tree_node(node, 1);
    //@ close tree_node(node, 1);
    node = tree_add_left(node);
    
    //@ open tree_node(node, 1);
    //@ close tree_node(node, 1);
    node = tree_add_right(node);
    
    //@ open tree_node(node, 1);
    //@ close tree_node(node, 1);
    node = tree_get_parent(node);
    
    //@ open tree_node(node, ?count1);
    //@ close tree_node(node, count1);
    node = tree_add_left(node);
    
    //@ open tree_node(node, 1);
    //@ close tree_node(node, 1);
    node = tree_get_parent(node);
    
    //@ open tree_node(node, ?count2);
    //@ close tree_node(node, count2);
    node = tree_get_parent(node);
    
    tree_dispose(node);
    return 0;
}
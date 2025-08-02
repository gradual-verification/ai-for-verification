#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a tree node
predicate tree_node(struct node *n; int depth) =
    n != 0 ?
        n->left |-> ?left &*&
        n->right |-> ?right &*&
        n->parent |-> ?parent &*&
        n->count |-> ?count &*&
        malloc_block_node(n) &*&
        (left == 0 ? true : tree_node(left, depth - 1) &*& left->parent |-> n) &*&
        (right == 0 ? true : tree_node(right, depth - 1) &*& right->parent |-> n) &*&
        count == 1 + (left == 0 ? 0 : left->count) + (right == 0 ? 0 : right->count) &*&
        depth > 0
    :
        true;

// Define a predicate for a root node (parent is null)
predicate root_tree_node(struct node *n; int depth) =
    n != 0 ?
        n->left |-> ?left &*&
        n->right |-> ?right &*&
        n->parent |-> 0 &*&
        n->count |-> ?count &*&
        malloc_block_node(n) &*&
        (left == 0 ? true : tree_node(left, depth - 1) &*& left->parent |-> n) &*&
        (right == 0 ? true : tree_node(right, depth - 1) &*& right->parent |-> n) &*&
        count == 1 + (left == 0 ? 0 : left->count) + (right == 0 ? 0 : right->count) &*&
        depth > 0
    :
        true;
@*/

/*`create_tree()` Function:
- Parameters: None.
- Description: This function creates a new tree.

It makes sure that the return value is a tree. */
struct node *create_tree()
//@ requires true;
//@ ensures root_tree_node(result, 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close root_tree_node(n, 1);
    return n;
}


/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
//@ requires node == 0 ? true : node->count |-> ?count;
//@ ensures node == 0 ? result == 0 : node->count |-> count &*& result == count;
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
//@ requires node != 0 &*& parent == 0 ? true : parent->left |-> ?left &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?oldcount;
//@ ensures parent == 0 ? true : parent->left |-> left &*& parent->right |-> right &*& parent->parent |-> grandparent &*& parent->count |-> ?newcount;
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
        if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        fixup_ancestors(parent, grandparent, parentCount);
    }
}


/*`tree_add_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function adds a new node
 as the left child of the input node.
 
It makes sure to return the new node in the tree.*/
struct node *tree_add_left(struct node *node)
//@ requires tree_node(node, ?depth);
//@ ensures tree_node(node, depth + 1) &*& result != 0 &*& result->parent |-> node;
{
    if (node == 0) {
        abort();
    }
    {
        //@ open tree_node(node, depth);
        struct node *n = malloc(sizeof(struct node));
        if (n == 0) {
            abort();
        }
        n->left = 0;
        n->right = 0;
        n->parent = node;
        n->count = 1;
        {
            struct node *nodeLeft = node->left;
            if (nodeLeft != 0) {
                abort();
            }
            node->left = n;
            if (n == node->right) {
                abort();
            }
            fixup_ancestors(n, node, 1);
        }
        //@ close tree_node(node, depth + 1);
        return n;
    }
}


/*`tree_add_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: It adds a new node as the right child 
of the input node by following a similar process 
of memory allocation, setting pointers, and 
updating count values. 

It makes sure to return the new node in the tree. */
struct node *tree_add_right(struct node *node)
//@ requires tree_node(node, ?depth);
//@ ensures tree_node(node, depth + 1) &*& result != 0 &*& result->parent |-> node;
{
    if (node == 0) {
        abort();
    }
    {
        //@ open tree_node(node, depth);
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
        //@ close tree_node(node, depth + 1);
        return n;
    }
}


/*tree_get_parent Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the parent node 

It makes sure to return the parent node in the tree. */
struct node *tree_get_parent(struct node *node)
//@ requires node != 0 &*& node->parent |-> ?parent &*& parent != 0;
//@ ensures node != 0 &*& node->parent |-> parent &*& parent != 0 &*& result == parent;
{
    if (node == 0) {
        abort();
    }
    {
        struct node *parent = node->parent;
        if (parent == 0) {
            abort();
        }
        return parent;
    }
}


/*`dispose_node()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function frees the memory allocated for the node and its subtree

It makes sure that the subtree of the node is freed. */
void dispose_node(struct node *node)
//@ requires node == 0 ? true : tree_node(node, _);
//@ ensures true;
{
    if (node == 0) {
    } else {
        //@ open tree_node(node, _);
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

/*`tree_dispose()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function disposes of the tree

It makes sure that the tree is freed. */
void tree_dispose(struct node *node)
//@ requires root_tree_node(node, _);
//@ ensures true;
{
    if (node == 0) {
        abort();
    }
    {
        //@ open root_tree_node(node, _);
        struct node *parent = node->parent;
        if (parent != 0) {
            abort();
        }
    }
    dispose_node(node);
}


// TODO: make this function pass the verification
/*`main()` Function:
- Parameters: None.
- Description: The main function creates a tree and
adds left and right children to the root node. It then
retrieves the parent of the right child and adds a left
child to it. It then retrieves the parent of the left child
and disposes of the tree. */
int main()
//@ requires true;
//@ ensures true;
{
    struct node *node = create_tree();
    //@ assert root_tree_node(node, 1);
    
    struct node *left_child = tree_add_left(node);
    //@ assert tree_node(node, 2);
    //@ assert left_child->parent |-> node;
    
    struct node *right_child = tree_add_right(node);
    //@ assert tree_node(node, 2);
    //@ assert right_child->parent |-> node;
    
    struct node *parent = tree_get_parent(right_child);
    //@ assert parent == node;
    
    struct node *left_of_parent = tree_add_left(parent);
    //@ assert tree_node(parent, 3);
    //@ assert left_of_parent->parent |-> parent;
    
    struct node *parent_of_left = tree_get_parent(left_of_parent);
    //@ assert parent_of_left == parent;
    
    struct node *root = tree_get_parent(parent_of_left);
    //@ assert root == node;
    
    tree_dispose(root);
    return 0;
}
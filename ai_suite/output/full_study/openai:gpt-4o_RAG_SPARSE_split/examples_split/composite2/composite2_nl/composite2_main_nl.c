#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate tree(struct node *n; int count) =
    n == 0 ?
        count == 0
    :
        n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &*& n->count |-> count &*&
        malloc_block_node(n) &*&
        tree(left, ?leftCount) &*& tree(right, ?rightCount) &*&
        count == 1 + leftCount + rightCount;

@*/

/*`create_tree()` Function:
- Parameters: None.
- Description: This function creates a new tree.

It makes sure that the return value is a tree. */
struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close tree(n, 1);
    return n;
}

/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires tree(node, ?count);
    //@ ensures tree(node, count) &*& result == count;
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
    //@ requires tree(node, ?nodeCount) &*& tree(parent, ?parentCount);
    //@ ensures tree(node, nodeCount) &*& tree(parent, ?newParentCount);
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

/*`tree_add_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function adds a new node
 as the left child of the input node.
 
It makes sure to return the new node in the tree.*/
struct node *tree_add_left(struct node *node)
    //@ requires tree(node, ?count);
    //@ ensures tree(result, 1) &*& tree(node, ?newCount);
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
        //@ close tree(n, 1);
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
    //@ requires tree(node, ?count);
    //@ ensures tree(result, 1) &*& tree(node, ?newCount);
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
        //@ close tree(n, 1);
        return n;
    }
}

/*tree_get_parent Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the parent node 

It makes sure to return the parent node in the tree. */
struct node *tree_get_parent(struct node *node)
    //@ requires tree(node, ?count);
    //@ ensures tree(node, count) &*& tree(result, ?parentCount);
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
    //@ requires tree(node, _);
    //@ ensures true;
{
    if (node == 0) {
    } else {
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
    //@ requires tree(node, _);
    //@ ensures true;
{
    if (node == 0) {
        abort();
    }
    {
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
    struct node *left = tree_add_left(node);
    struct node *right = tree_add_right(node);
    struct node *parent = tree_get_parent(right);
    struct node *leftChild = tree_add_left(parent);
    struct node *root = tree_get_parent(leftChild);
    tree_dispose(root);
    return 0;
}
#include "malloc.h"
#include <stdbool.h>
#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};


/*`create_tree()` Function:
- Parameters: None.
- Description: This function creates a new tree.

It makes sure that the return value is a tree. */
struct node *create_tree()
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    return n;
}

/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
{
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    return result;
}

/*`tree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function is used to get the 
count value of the tree starting from the given node.

This function makes sure that the tree of node is not changed. */
int tree_get_count(struct node *node)
{
    int result = subtree_get_count(node);
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

/*tree_get_parent Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the parent node 

It makes sure to return the parent node in the tree. */
struct node *tree_get_parent(struct node *node)
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

/*`tree_get_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the left child node 

It makes sure to return the left node in the tree. */
struct node *tree_get_left(struct node *node)
{
    if (node == 0) {
        abort();
    }
    {
        struct node *left = node->left;
        return left;
    }
}

/*`tree_get_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the right child node 

It makes sure to return the right node in the tree. */
struct node *tree_get_right(struct node *node)
{
    if (node == 0) {
        abort();
    }
    {
        struct node *right = node->right;
        return right;
    }
}

/*`tree_has_parent()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a parent

It makes sure that the tree is not changed. */
bool tree_has_parent(struct node *node)
{
    bool result = false;
    if (node == 0) {
    } else {
        struct node *parent = node->parent;
        result = parent != 0;
    }
    return result;
}

/*`tree_has_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a left child

It makes sure that the tree is not changed. */
bool tree_has_left(struct node *node)
{
    bool result = false;
    if (node == 0) {
    } else {
        struct node *left = node->left;
        result = left != 0;
    }
    return result;
}

/*`tree_has_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function checks if the node has a right child 

It makes sure that the tree is not changed. */
bool tree_has_right(struct node *node)
{
    bool result = false;
    if (node == 0) {
    } else {
        struct node *right = node->right;
        result = right != 0;
    }
    return result;
}

/*`dispose_node()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function frees the memory allocated for the node and its subtree

It makes sure that the subtree of the node is freed. */
void dispose_node(struct node *node)
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

/*`main()` Function:
- Parameters: None.
- Description: The main function creates a tree and
adds left and right children to the root node. It then
retrieves the parent of the right child and adds a left
child to it. It then retrieves the parent of the left child
and disposes of the tree. */
int main()
{
    struct node *node = create_tree();
    node = tree_add_left(node);
    node = tree_add_right(node);
    node = tree_get_parent(node);
    node = tree_add_left(node);
    node = tree_get_parent(node);
    node = tree_get_parent(node);
    tree_dispose(node);
    return 0;
}
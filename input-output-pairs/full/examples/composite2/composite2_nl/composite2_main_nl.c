#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



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


// TODO: make this function pass the verification
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
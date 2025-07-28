#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};



/*tree_add_right function
-param: struct node *node
-description: The function adds a right node to the
current node. It requires that before the call, the current node is non-null and its right node is null.
It returns the newly added node and makes sure that it is the right child of the given node.
*/
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
        struct node *nodeRight = node->right;
        node->right = n;
        fixup_ancestors(n, node, 1);
    }
    return n;
}


/*tree_dispose function
-param: struct node *node
-description: The function disposes the tree by calling 
the dispose_node function.

It makes sure that the tree of noed is freed.
*/
void tree_dispose(struct node *node)
{
    dispose_node(node);
}


/*create_tree function
-param: void
-description: The function creates a tree with one node and returns it.

It makes sure that the returned value is a tree with one node.
*/
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


/*tree_get_parent function
-param: struct node *node
-description: The function gets the parent of the
current node. It requires that before the call, the current node and its parent are non-null.
It makes sure that the returned value is the parent of the current node and the tree is not changed.
*/
struct node *tree_get_parent(struct node *node)
{
    struct node *parent = node->parent;
    return parent;
}


/*tree_add_left function
-param: struct node *node
-description: The function adds a left node to the
current node. It requires that before the call, the current node is non-null and its left node is null.
It returns the newly added node and makes sure that it is the left child of the given node.
*/
struct node *tree_add_left(struct node *node)
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
        node->left = n;
        fixup_ancestors(n, node, 1);
    }
    return n;
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

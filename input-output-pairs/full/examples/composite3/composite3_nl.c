#include "malloc.h"
#include <stdbool.h>

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*abort function
-param: void
-description: The function aborts the program.
*/
void abort();

/*create_tree function
-param: void
-description: The function creates a tree and returns it.
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

/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node.
*/
int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?parent, ?nodes);
    //@ ensures subtree(node, parent, nodes);
{
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    return result;
}

/*tree_get_count function
-param: struct node *node
-description: The function gets the count of the current node.
*/
int tree_get_count(struct node *node)
{
    int result = subtree_get_count(node);
    return result;
}

/*fixup_ancestors function
-param: struct node *node, struct node *parent, int count
-description: The function fixes the count of the ancestors
of the current node.
*/
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
        {
            if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            fixup_ancestors(parent, grandparent, parentCount);
        }
    }
}

/*tree_add_left function
-param: struct node *node
-description: The function adds a left node to the
current node.
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

/*tree_add_right function
-param: struct node *node
-description: The function adds a right node to the
current node.
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

/*tree_get_parent function
-param: struct node *node
-description: The function gets the parent of the
current node.
*/
struct node *tree_get_parent(struct node *node)
{
    struct node *parent = node->parent;
    /*@ switch (contextNodes) {
            case root:
            case left_context(parentContextNodes1, parent0, rightNodes):
                close subtree(parent, grandparent, tree(parent, subtreeNodes, rightNodes));
            case right_context(parentContextNodes1, parent0, leftNodes):
                close subtree(parent, grandparent, tree(parent, leftNodes, subtreeNodes));
        }
    @*/
    return parent;
}

/*tree_get_left function
-param: struct node *node
-description: The function gets the left node of the
current node.
*/
struct node *tree_get_left(struct node *node)
    /*@ requires tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return leftNodes != empty;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, left_context(contextNodes, node, rightNodes), leftNodes);
            };
    @*/
{
    struct node *left = node->left;
    return left;
}

/*tree_get_right function
-param: struct node *node
-description: The function gets the right node of the
current node.
*/
struct node *tree_get_right(struct node *node)
{
    struct node *right = node->right;
    return right;
}

/*tree_has_parent function
-param: struct node *node
-description: The function checks if the parent of the
current node is not empty.
*/
bool tree_has_parent(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes) &*& subtreeNodes != empty;
    //@ ensures tree(node, contextNodes, subtreeNodes) &*& result == (contextNodes != root);
{
    struct node *parent1 = node->parent;
    return parent1 != 0;
}

/*tree_has_left function
-param: struct node *node
-description: The function checks if the left node of the
current node is not empty.
*/
bool tree_has_left(struct node *node)
    /*@ ensures
            tree(node, contextNodes, subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return result == (leftNodes != empty);
            };
    @*/
{
    struct node *left = node->left;
    return left != 0;
}

/*tree_has_right function
-param: struct node *node
-description: The function checks if the right node of the
current node is not empty.
*/
bool tree_has_right(struct node *node)
{
    struct node *right = node->right;
    return right != 0;
}

/*dispose_node function
-param: struct node *node
-description: The function disposes the tree by calling
itself recursively on the left and right nodes of the
current node. It then frees the current node.
*/
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

/*tree_dispose function
-param: struct node *node
-description: The function disposes the tree by calling 
the dispose_node function.
*/
void tree_dispose(struct node *node)
{
    dispose_node(node);
}

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

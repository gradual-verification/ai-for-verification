#include "malloc.h"
#include <stdbool.h>

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*
  Natural Language Specification:
  - Description: Terminates the program abnormally. This function is used to handle allocation failure by terminating the program.
  - Parameters: None.
  - Requires: True.
  - Ensures: False.
*/
void abort();
   
/*
  Natural Language Specification:
  - Description: Allocates memory for a new node, initializes its fields, and creates a tree with this node as the root. If memory allocation fails, it calls `abort()`.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: Returns a pointer to a newly created tree with a single root node.
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
/*
  Natural Language Specification:
  - Description: Returns the count of nodes in the subtree rooted at the given node. If the node is null, the count is zero.
  - Parameters: `node` - a pointer to the root of the subtree.
  - Requires: The `node` must be part of a valid subtree.
  - Ensures: Returns the count of nodes in the subtree.
*/
int subtree_get_count(struct node *node)
{
    int result = 0;
   
    if (node == 0) {
    } else {
        result = node->count;
    }
    
    return result;
}
/*
  Natural Language Specification:
  - Description: Returns the count of nodes in the entire tree by calling `subtree_get_count`.
  - Parameters: `node` - a pointer to the root of the tree.
  - Requires: The `node` must be part of a valid tree.
  - Ensures: Returns the count of nodes in the tree.
*/
int tree_get_count(struct node *node)
    
{
    
    int result = subtree_get_count(node);
    
    return result;
}
/*
  Natural Language Specification:
  - Description: Recursively updates the count of nodes in the subtree for all ancestors of the given node, ensuring that each ancestor node's count field is correctly updated.
  - Parameters: 
    - `node` - a pointer to the current node.
    - `parent` - a pointer to the parent node.
    - `count` - the updated count of the current node.
  - Requires: A valid context for the given node and its parent.
  - Ensures: Updates the count of nodes in the subtree for all ancestors of the given node.
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
        if (node == left) {
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else {
            leftCount = subtree_get_count(left);
            rightCount = count;
        }
        {
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            fixup_ancestors(parent, grandparent, parentCount);
        }
    }
    
}
/*
  Natural Language Specification:
  - Description: Allocates memory for a new left child node, initializes its fields, and attaches it to the given node as the left child. It updates the ancestor counts accordingly. If memory allocation fails, it calls `abort()`.
  - Parameters: `node` - a pointer to the node where the new left child will be added.
  - Requires: 
    - The given node must be part of a valid tree.
    - Its left subtree must be empty.
  - Ensures: Returns a new left child node.
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
/*
  Natural Language Specification:
  - Description: Allocates memory for a new right child node, initializes its fields, and attaches it to the given node as the right child. It updates the ancestor counts accordingly. If memory allocation fails, it calls `abort()`.
  - Parameters: `node` - a pointer to the node where the new right child will be added.
  - Requires: 
    - The given node must be part of a valid tree.
    - Its right subtree must be empty.
  - Ensures: Returns a new right child node.
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
/*
  Natural Language Specification:
  - Description: Returns the parent of the given node, updating the tree context to reflect this change.
  - Parameters: `node` - a pointer to the current node.
  - Requires: 
    - The given node must be part of a valid tree.
    - The node must not be the root node.
  - Ensures: Returns the parent of the given node.
*/
struct node *tree_get_parent(struct node *node)
   
{
    
    struct node *parent = node->parent;
    
    return parent;
}
/*
  Natural Language Specification:
  - Description: Returns the left child node of the given node, updating the tree context to reflect this change.
  - Parameters: `node` - a pointer to the current node.
  - Requires: 
    - The given node must be part of a valid tree.
    - Its left subtree must not be empty.
  - Ensures: Returns the left child node.
*/

struct node *tree_get_left(struct node *node)
   
{
   
    struct node *left = node->left;
   
    return left;
}
/*
  Natural Language Specification:
  - Description: Returns the right child node of the given node, updating the tree context to reflect this change.
  - Parameters: `node` - a pointer to the current node.
  - Requires: 
    - The given node must be part of a valid tree.
    - Its right subtree must not be empty.
  - Ensures: Returns the right child node.
*/
struct node *tree_get_right(struct node *node)
   
{
    
    struct node *right = node->right;
    
    return right;
}
/*
  Natural Language Specification:
  - Description: Checks if the given node has a parent and returns true if it does, false otherwise.
  - Parameters: `node` - a pointer to the current node.
  - Requires: 
    - The given node must be part of a valid tree.
    - The node must not be the root node.
  - Ensures: Returns true if the given node has a parent, false otherwise.
*/
bool tree_has_parent(struct node *node)
    
{
    
    struct node *parent = node->parent;
    
    return parent != 0;
}
/*
  Natural Language Specification:
  - Description: Checks if the given node has a left child and returns true if it does, false otherwise.
  - Parameters: `node` - a pointer to the current node.
  - Requires: The given node must be part of a valid tree.
  - Ensures: Returns true if the given node has a left child, false otherwise.
*/
bool tree_has_left(struct node *node)
   
{
    
    struct node *left = node->left;
   
    return left != 0;
}
/*
  Natural Language Specification:
  - Description: Checks if the given node has a right child and returns true if it does, false otherwise.
  - Parameters: `node` - a pointer to the current node.
  - Requires: The given node must be part of a valid tree.
  - Ensures: Returns true if the given node has a right child, false otherwise.
*/
bool tree_has_right(struct node *node)
   
{
    
    struct node *right = node->right;
    
    return right != 0;
}
/*
  Natural Language Specification:
  - Description: Recursively frees all memory associated with the subtree rooted at the given node.
  - Parameters: `node` - a pointer to the root of the subtree to be disposed.
  - Requires: The `node` must be part of a valid subtree.
  - Ensures: Frees all memory associated with the subtree.
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
/*
  Natural Language Specification:
  - Description: Frees all memory associated with the tree rooted at the given node by calling `dispose_node`.
  - Parameters: `node` - a pointer to the root of the tree to be disposed.
  - Requires: The `node` must be part of a valid tree.
  - Ensures: Frees all memory associated with the tree.
*/
void tree_dispose(struct node *node)
   
{
    
    dispose_node(node);
}
/*
  Natural Language Specification:
  - Description: Creates a binary tree, adds left and right children to the nodes, retrieves parents and children, and then disposes of the tree.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: No specific postconditions.
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

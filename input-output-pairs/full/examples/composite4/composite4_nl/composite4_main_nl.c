#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};


/***
 * Description:
The tree_add_right function adds a new right child to the specified node in the tree.

@param `node` - a pointer to the node to which the right child will be added.

Requires: 
  - The tree rooted at `node` is valid.
  - The right subtree of `node` is null.
Ensures: Returns a pointer to the newly added right child, and the tree is correctly updated.
*/
struct node *tree_add_right(struct node *node)
{
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        fixup_ancestors(n, node, 1);
    }
    return n;
}


/***
 * Description:
The tree_dispose function frees all memory associated with the tree rooted at the specified node.

@param `node` - a pointer to the root of the tree to be disposed.

Requires: The tree rooted at `node` is valid.
Ensures: All memory associated with the tree is freed.
*/
void tree_dispose(struct node *node)
{
  subtree_dispose(node);
}


/***
 * Description: 
The create_tree function creates a new tree with a single root node.

@param None.

Requires: No specific preconditions.
Ensures: Returns a pointer to the root node of the newly created tree.
*/
struct node *create_tree()
{
  struct node *n = create_node(0);
  return n;
}


/***
 * Description: 
The tree_get_parent function retrieves the parent node of the specified node in the tree.

@param `node` - a pointer to the current node.

Requires: 
  - `node` is not null. 
Ensures: Returns the parent node of `node` and ensures the tree structure is unchanged.
*/
struct node *tree_get_parent(struct node *node)
{
  struct node *p = node->parent;
  return p;
}


/***
 * Description:
The tree_add_left function adds a new left child to the specified node in the tree.

@param `node` - a pointer to the node to which the left child will be added.

Requires: 
  - The tree rooted at `node` is valid.
  - The left subtree of `node` is null.
Ensures: Returns a pointer to the newly added left child, and the tree is correctly updated.
*/
struct node *tree_add_left(struct node *node)
{
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      fixup_ancestors(n, node, 1);
  }
  return n;
}


// TODO: make this function pass the verification
/***
* Description:
The main function demonstrates various operations on a binary tree, including adding nodes, retrieving parent nodes, and disposing of the tree.
*/
int main() //@ : main
{
    struct node *root = create_tree();
    struct node *left = tree_add_left(root);
    struct node *leftRight = tree_add_right(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    struct node *leftLeft = tree_add_left(left);
    struct node *leftRightRight = tree_add_right(leftRight);
    tree_dispose(root);
    return 0;
}

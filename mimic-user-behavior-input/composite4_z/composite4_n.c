
#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};



/*
  Natural Language Specification:
  - Description: Creates a new node in the tree with the specified parent node, and initializes its left and right children as empty.
  - Parameters: `p` - a pointer to the parent node.
  - Requires: No specific preconditions.
  - Ensures: Returns a pointer to the newly created node, and the subtree rooted at this node is correctly initialized.
*/
struct node *create_node(struct node *p)
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->count = 1;
  
  return n;
}

/*
  Natural Language Specification:
  - Description: Creates a new tree with a single root node.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: Returns a pointer to the root node of the newly created tree.
*/
struct node *create_tree()
{
  struct node *n = create_node(0);
 
  return n;
}

/*
  Natural Language Specification:
  - Description: Retrieves the count of nodes in the subtree rooted at the specified node.
  - Parameters: `node` - a pointer to the root of the subtree.
  - Requires: The subtree rooted at `node` is valid.
  - Ensures: Returns the count of nodes in the subtree and ensures it is non-negative.
*/
int subtree_get_count(struct node *node)
  
{
  int result = 0;
 
  if (node != 0) { result = node->count; }
 
  return result;
}

/*
  Natural Language Specification:
  - Description: Updates the count of nodes in the subtree for all ancestor nodes starting from the specified node.
  - Parameters: 
    - `n` - a pointer to the current node.
    - `p` - a pointer to the parent node.
    - `count` - the updated count of nodes in the subtree rooted at the current node.
  - Requires: The context of the node and its parent is valid, and the count is non-negative.
  - Ensures: The context is updated with the correct count, and the node's left child remains unchanged.
*/
void fixup_ancestors(struct node *n, struct node *p, int count)
{
 
  if (p == 0) {
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
     
      leftCount = count;
      rightCount = subtree_get_count(right);
    } else {
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
    }
  }
 
}

/*
  Natural Language Specification:
  - Description: Adds a new left child to the specified node in the tree.
  - Parameters: `node` - a pointer to the node to which the left child will be added.
  - Requires: 
    - The tree rooted at `node` is valid.
    - The left subtree of `node` is empty.
  - Ensures: Returns a pointer to the newly added left child, and the tree is correctly updated.
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

/*
  Natural Language Specification:
  - Description: Adds a new right child to the specified node

 in the tree.
  - Parameters: `node` - a pointer to the node to which the right child will be added.
  - Requires: 
    - The tree rooted at `node` is valid.
    - The right subtree of `node` is empty.
  - Ensures: Returns a pointer to the newly added right child, and the tree is correctly updated.
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

/*
  Natural Language Specification:
  - Description: Retrieves the parent node of the specified node in the tree.
  - Parameters: `node` - a pointer to the current node.
  - Requires: 
    - The tree rooted at `node` is valid.
    - `node` is not the root of the tree.
  - Ensures: Returns the parent node of `node`, and the tree is correctly updated.
*/
struct node *tree_get_parent(struct node *node)
{
  
  struct node *p = node->parent;
  
  return p;
}

/*
  Natural Language Specification:
  - Description: Recursively frees all memory associated with the subtree rooted at the specified node.
  - Parameters: `node` - a pointer to the root of the subtree to be disposed.
  - Requires: The subtree rooted at `node` is valid.
  - Ensures: All memory associated with the subtree is freed.
*/
void subtree_dispose(struct node *node)

{
  
  if (node != 0) {
    {
      struct node *left = node->left;
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    free(node);
  }
}

/*
  Natural Language Specification:
  - Description: Frees all memory associated with the tree rooted at the specified node.
  - Parameters: `node` - a pointer to the root of the tree to be disposed.
  - Requires: The tree rooted at `node` is valid.
  - Ensures: All memory associated with the tree is freed.
*/
void tree_dispose(struct node *node)
 
{
  
  subtree_dispose(node);
}

/*
  Natural Language Specification:
  - Description: Main function that creates a tree, adds left and right children, and then disposes of the tree.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: No specific postconditions.
*/
int main0()

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



/*
  Natural Language Specification:
  - Description: Main function that demonstrates various operations on a binary tree, including adding nodes, retrieving parent nodes, and disposing of the tree.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: No specific postconditions.
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

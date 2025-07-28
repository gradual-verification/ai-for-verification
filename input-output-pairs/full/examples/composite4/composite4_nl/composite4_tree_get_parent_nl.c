#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};


// TODO: make this function pass the verification
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


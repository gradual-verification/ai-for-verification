#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};


/*add_to_count function
-param: struct node *p, int delta
-description: This function adds the delta value to the count of the node p and its parent nodes,
where count is the number of nodes in the subtree rooted at the node.

It requires that p is non-null and in a tree, and all nodes in its subtree except p itself are valid nodes. 
p's count will be valid after adding delta (>0) to it. So it ensures that the tree is valid after the operation.
*/
void add_to_count(struct node *p, int delta)
{
  struct node *pp = p->parent;
 
  if (pp == 0) {
    p->count += delta;

  } else {
    
    p->count += delta;
    
    add_to_count(pp, delta);
  }
}


/*create_node function
-param: struct node *p, struct node *next
-description: This function creates a new node with a specified parent and next sibling.
The node is initialized with an empty list of children and a count of 1.
It returns a pointer to the newly created node, which is properly initialized.
*/
struct node *create_node(struct node *p, struct node *next)
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  return n;
}


// TODO: make this function pass the verification
/*tree_add function
-param: struct node *node
-description: This function adds a new node to the tree. 
It returns the newly added node.
It requires that the node is a part of valid tree. 
It ensures that the tree is still valid after adding a node.
*/
struct node *tree_add(struct node *node)
{
  
  struct node *n = create_node(node, node->firstChild);
  node->firstChild = n;
  
  add_to_count(node, 1);

  return n;
}


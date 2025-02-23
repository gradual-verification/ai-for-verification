#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

/*create_node function
-param: struct node *p, struct node *next
-description: This function creates a new node
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

/*create_tree function
-param: none
-description: This function creates a new tree
*/
struct node *create_tree()
{
  struct node *n = create_node(0, 0);
  return n;
}


/*add_to_count function
-param: struct node *p, int delta
-description: This function adds the delta value to the count of the node p and its parent nodes
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

/*tree_add function
-param: struct node *node
-description: This function adds a new node to the tree
*/
struct node *tree_add(struct node *node)
{
  
  struct node *n = create_node(node, node->firstChild);
  node->firstChild = n;
  
  add_to_count(node, 1);

  return n;
}
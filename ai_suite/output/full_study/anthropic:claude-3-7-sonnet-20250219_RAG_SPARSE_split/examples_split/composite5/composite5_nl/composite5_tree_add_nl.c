#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@
// Define a predicate for a valid tree node
predicate tree_node(struct node *n, int count) =
    n != 0 &*&
    n->firstChild |-> ?fc &*&
    n->nextSibling |-> ?ns &*&
    n->parent |-> ?p &*&
    n->count |-> count &*&
    malloc_block_node(n) &*&
    count > 0;

// Define a predicate for a valid tree
predicate tree(struct node *n, int count) =
    n == 0 ?
        count == 0
    :
        tree_node(n, count) &*&
        tree(n->firstChild, ?fcCount) &*&
        tree(n->nextSibling, ?nsCount) &*&
        count == 1 + fcCount + nsCount;
@*/

/*create_node function
-param: struct node *p, struct node *next
-description: This function creates a new node with a specified parent and next sibling.
The node is initialized with an empty list of children and a count of 1.
It returns a pointer to the newly created node, which is properly initialized.
*/
struct node *create_node(struct node *p, struct node *next)
//@ requires true;
//@ ensures tree_node(result, 1) &*& result->firstChild |-> 0 &*& result->nextSibling |-> next &*& result->parent |-> p;
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  //@ close tree_node(n, 1);
  return n;
}


/*add_to_count function
-param: struct node *p, int delta
-description: This function adds the delta value to the count of the node p and its parent nodes,
where count is the number of nodes in the subtree rooted at the node.

It requires that p is non-null and in a tree, and all nodes in its subtree except p itself are valid nodes. 
p's count will be valid after adding delta (>0) to it. So it ensures that the tree is valid after the operation.
*/
void add_to_count(struct node *p, int delta)
//@ requires tree_node(p, ?count) &*& delta > 0 &*& count + delta > 0;
//@ ensures tree_node(p, count + delta);
{
  struct node *pp = p->parent;
  //@ open tree_node(p, count);
 
  if (pp == 0) {
    p->count += delta;
    //@ close tree_node(p, count + delta);
  } else {
    p->count += delta;
    //@ close tree_node(p, count + delta);
    
    //@ open tree_node(pp, ?ppCount);
    //@ close tree_node(pp, ppCount);
    add_to_count(pp, delta);
  }
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
//@ requires tree_node(node, ?count) &*& node->firstChild |-> ?fc;
//@ ensures tree_node(node, count + 1) &*& tree_node(result, 1) &*& result->parent |-> node &*& result->firstChild |-> 0 &*& result->nextSibling |-> fc;
{
  struct node *n = create_node(node, node->firstChild);
  //@ open tree_node(node, count);
  node->firstChild = n;
  //@ close tree_node(node, count);
  
  add_to_count(node, 1);

  return n;
}
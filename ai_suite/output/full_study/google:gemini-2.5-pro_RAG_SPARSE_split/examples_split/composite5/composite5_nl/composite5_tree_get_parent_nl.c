#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@

// A forest is a list of sibling trees.
// This predicate represents a forest starting at node 'n', where all root nodes of the forest have parent 'p'.
// It recursively defines the ownership and structure of the entire forest, including all descendants.
predicate forest(struct node *n, struct node *p) =
    n == 0 ?
        true
    :
        n->firstChild |-> ?fc &*&
        n->nextSibling |-> ?ns &*&
        n->parent |-> p &*&
        n->count |-> ?c &*&
        malloc_block_node(n) &*&
        // The children of 'n' form a forest where 'n' is the parent.
        forest(fc, n) &*&
        // The next sibling of 'n' continues the current forest with the same parent 'p'.
        forest(ns, p);

@*/


// TODO: make this function pass the verification
/*tree_get_parent function
-param: struct node *node
-description: This function gets and returns the parent node a new node of the current node.
It requires that the node is a part of valid tree. 
It ensures that the tree is still valid, and the returned node is null or in the tree.
*/
struct node *tree_get_parent(struct node *node)
    //@ requires node != 0 &*& forest(node, ?parent_node);
    //@ ensures forest(node, parent_node) &*& result == parent_node;
{
  //@ open forest(node, parent_node);
  struct node *p = node->parent;
  //@ close forest(node, parent_node);
  
  return p;
}
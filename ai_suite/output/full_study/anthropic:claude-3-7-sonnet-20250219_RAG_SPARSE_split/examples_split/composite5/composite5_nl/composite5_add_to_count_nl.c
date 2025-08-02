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
predicate node_valid(struct node *n, int subtree_count) =
    n != 0 &*&
    n->firstChild |-> ?fc &*&
    n->nextSibling |-> ?ns &*&
    n->parent |-> ?p &*&
    n->count |-> subtree_count &*&
    malloc_block_node(n);

// Define a predicate for a node in a tree
predicate node_in_tree(struct node *n, int id, int subtree_count) =
    node_valid(n, subtree_count) &*&
    ghost_list_member_handle(id, n);

// Define a predicate for a tree
predicate tree(int id, struct node *root) =
    ghost_list(id, ?nodes) &*&
    root == 0 ? true : node_in_tree(root, id, _);
@*/

// TODO: make this function pass the verification
/*add_to_count function
-param: struct node *p, int delta
-description: This function adds the delta value to the count of the node p and its parent nodes,
where count is the number of nodes in the subtree rooted at the node.

It requires that p is non-null and in a tree, and all nodes in its subtree except p itself are valid nodes. 
p's count will be valid after adding delta (>0) to it. So it ensures that the tree is valid after the operation.
*/
void add_to_count(struct node *p, int delta)
/*@
requires 
    p != 0 &*& 
    node_valid(p, ?count) &*& 
    delta > 0;
ensures 
    node_valid(p, count + delta);
@*/
{
  struct node *pp = p->parent;
 
  if (pp == 0) {
    //@ open node_valid(p, count);
    p->count += delta;
    //@ close node_valid(p, count + delta);

  } else {
    //@ open node_valid(p, count);
    p->count += delta;
    //@ close node_valid(p, count + delta);
    
    add_to_count(pp, delta);
  }
}
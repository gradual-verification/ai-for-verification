#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};


/***
 * Description:
The subtree_get_count function retrieves the count of nodes in the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree.

Requires: The subtree rooted at `node` is valid.
Ensures: Returns the count of nodes in the subtree and ensures it is non-negative.
*/
/*@
predicate node_count(struct node *node, int count) =
  node == 0 ?
    count == 0
  :
    node->count |-> count &*& count >= 0;

predicate node_tree(struct node *node) =
  node == 0 ?
    true
  :
    node->left |-> ?left &*& 
    node->right |-> ?right &*& 
    node->parent |-> ?parent &*& 
    node->count |-> ?count &*& 
    count >= 0 &*&
    node_tree(left) &*& 
    node_tree(right) &*&
    malloc_block_node(node);
@*/

int subtree_get_count(struct node *node)
  //@ requires node_tree(node) &*& node_count(node, ?count);
  //@ ensures node_tree(node) &*& node_count(node, count) &*& result == count &*& result >= 0;
{
  int result = 0;
  if (node != 0) { 
    //@ open node_tree(node);
    //@ open node_count(node, count);
    result = node->count; 
    //@ close node_count(node, count);
    //@ close node_tree(node);
  } else {
    //@ open node_count(node, count);
    //@ close node_count(node, count);
  }
  return result;
}


// TODO: make this function pass the verification
/***
 * Description:
The fixup_ancestors function updates the count of nodes in the subtree for all ancestor nodes starting from the specified node.

@param `n` - a pointer to the current node.
@param `p` - a pointer to the parent node.
@param `count` - the updated count of nodes in the subtree rooted at the current node.

Requires: The parent node is the parent of the current node, and the count is non-negative.
Ensures: The ancestor nodes are updated with the correct count.
*/
void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires node_tree(n) &*& node_tree(p) &*& count >= 0 &*& (n == 0 || n->parent |-> p);
  //@ ensures node_tree(n) &*& node_tree(p);
{
  if (p == 0) {
    // Base case: no parent to update
  } else {
    //@ open node_tree(p);
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      //@ close node_tree(p);
      rightCount = subtree_get_count(right);
      //@ open node_tree(p);
    } else {
      //@ close node_tree(p);
      leftCount = subtree_get_count(left);
      //@ open node_tree(p);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close node_tree(p);
      fixup_ancestors(p, grandparent, pcount);
    }
  }
}
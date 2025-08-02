#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// Define a predicate for a binary tree node
predicate tree(struct node *n; int count, list<struct node *> children) =
    n == 0 ?
        count == 0 &*& children == nil
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> ?p &*&
        n->count |-> count &*&
        malloc_block_node(n) &*&
        tree(l, ?lcount, ?lchildren) &*&
        tree(r, ?rcount, ?rchildren) &*&
        count == 1 + lcount + rcount &*&
        children == append(lchildren, cons(n, rchildren));
@*/

/***
* Description:
The create_node function creates a new node in the tree with the specified parent node, and initializes its left and right children as empty.

@param `p` - a pointer to the parent node.

Requires: No specific preconditions.
Ensures: Returns a pointer to the newly created node, and the subtree rooted at this node is correctly initialized.
*/
struct node * create_node(struct node * p)
//@ requires true;
//@ ensures tree(result, 1, cons(result, nil)) &*& result->parent |-> p;
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close tree(0, 0, nil);
  //@ close tree(0, 0, nil);
  //@ close tree(n, 1, cons(n, nil));
  return n;
}


/***
 * Description:
The subtree_get_count function retrieves the count of nodes in the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree.

Requires: The subtree rooted at `node` is valid.
Ensures: Returns the count of nodes in the subtree and ensures it is non-negative.
*/
int subtree_get_count(struct node *node)
//@ requires node == 0 ? true : node->count |-> ?c;
//@ ensures node == 0 ? result == 0 : node->count |-> c &*& result == c;
{
  int result = 0;
  if (node != 0) { result = node->count; }
  return result;
}


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
//@ requires p == 0 ? true : p->left |-> ?l &*& p->right |-> ?r &*& p->parent |-> ?gp &*& p->count |-> ?oldcount;
//@ ensures p == 0 ? true : p->left |-> l &*& p->right |-> r &*& p->parent |-> gp &*& p->count |-> ?newcount;
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


// TODO: make this function pass the verification
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
//@ requires node != 0 &*& node->left |-> ?l &*& node->right |-> 0 &*& node->parent |-> ?p &*& node->count |-> ?c;
//@ ensures node != 0 &*& node->left |-> l &*& node->right |-> result &*& node->parent |-> p &*& node->count |-> ?newc &*& result->parent |-> node &*& tree(result, 1, cons(result, nil));
{
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        fixup_ancestors(n, node, 1);
    }
    return n;
}
#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// Predicate to represent a tree rooted at a node
predicate tree(struct node *node; list<struct node *> children) =
  node == 0 ?
    children == nil
  :
    node->left |-> ?left &*&
    node->right |-> ?right &*&
    node->parent |-> ?parent &*&
    node->count |-> ?count &*&
    malloc_block_node(node) &*&
    tree(left, ?leftChildren) &*&
    tree(right, ?rightChildren) &*&
    count == 1 + subtree_get_count(left) + subtree_get_count(right) &*&
    children == append(leftChildren, cons(node, rightChildren));
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
//@ ensures result != 0 &*& result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> p &*& result->count |-> 1 &*& malloc_block_node(result);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
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
//@ requires true;
//@ ensures result >= 0;
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
//@ requires p == 0 ? true : p->left |-> ?left &*& p->right |-> ?right &*& p->parent |-> ?grandparent &*& p->count |-> ?oldCount &*& count >= 0;
//@ ensures p == 0 ? true : p->left |-> left &*& p->right |-> right &*& p->parent |-> grandparent &*& p->count |-> ?newCount &*& newCount >= 0;
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
The tree_add_left function adds a new left child to the specified node in the tree.

@param `node` - a pointer to the node to which the left child will be added.

Requires: 
  - The tree rooted at `node` is valid.
  - The left subtree of `node` is null.
Ensures: Returns a pointer to the newly added left child, and the tree is correctly updated.
*/
struct node *tree_add_left(struct node *node)
//@ requires node != 0 &*& node->left |-> 0 &*& node->right |-> ?right &*& node->parent |-> ?parent &*& node->count |-> ?count;
//@ ensures node != 0 &*& node->left |-> result &*& node->right |-> right &*& node->parent |-> parent &*& node->count |-> (count + 1) &*& result != 0 &*& result->left |-> 0 &*& result->right |-> 0 &*& result->parent |-> node &*& result->count |-> 1 &*& malloc_block_node(result);
{
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      fixup_ancestors(n, node, 1);
  }
  return n;
}
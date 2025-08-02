#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
  n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count &*&
  malloc_block_node(n);

predicate tree(struct node *n; struct node *parent) =
  n == 0 ? true : node(n, ?left, ?right, parent, ?count) &*& tree(left, n) &*& tree(right, n);

fixpoint int subtree_count(struct node *n) {
  return n == 0 ? 0 : 1 + subtree_count(n->left) + subtree_count(n->right);
}

lemma void subtree_count_nonnegative(struct node *n)
  requires tree(n, ?parent);
  ensures tree(n, parent) &*& 0 <= subtree_count(n);
{
  open tree(n, parent);
  if (n != 0) {
    subtree_count_nonnegative(n->left);
    subtree_count_nonnegative(n->right);
  }
  close tree(n, parent);
}

lemma void subtree_count_correct(struct node *n)
  requires tree(n, ?parent);
  ensures tree(n, parent) &*& n != 0 ? n->count == subtree_count(n) : true;
{
  open tree(n, parent);
  if (n != 0) {
    subtree_count_correct(n->left);
    subtree_count_correct(n->right);
    assert node(n, ?left, ?right, parent, ?count);
    assert count == 1 + subtree_count(left) + subtree_count(right);
  }
  close tree(n, parent);
}

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
  //@ ensures node(result, 0, 0, p, 1) &*& tree(result, p);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close node(n, 0, 0, p, 1);
  //@ close tree(n, p);
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
  //@ requires tree(node, ?parent);
  //@ ensures tree(node, parent) &*& 0 <= result;
{
  int result = 0;
  if (node != 0) {
    //@ open tree(node, parent);
    result = node->count;
    //@ close tree(node, parent);
  }
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
  //@ requires tree(n, p) &*& tree(p, ?grandparent) &*& 0 <= count;
  //@ ensures tree(n, p) &*& tree(p, grandparent);
{
  if (p == 0) {
    //@ open tree(n, p);
    //@ close tree(n, p);
  } else {
    //@ open tree(n, p);
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
    //@ close tree(n, p);
    //@ close tree(p, grandparent);
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
  //@ requires tree(node, ?parent) &*& node->left |-> 0;
  //@ ensures tree(node, parent) &*& tree(result, node);
{
  struct node *n = create_node(node);
  {
    //@ open tree(node, parent);
    struct node *nodeLeft = node->left;
    node->left = n;
    fixup_ancestors(n, node, 1);
    //@ close tree(node, parent);
  }
  return n;
}
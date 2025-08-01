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
  //@ ensures tree(result, p);
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
The create_tree function creates a new tree with a single root node.

@param None.

Requires: No specific preconditions.
Ensures: Returns a pointer to the root node of the newly created tree.
*/
struct node *create_tree()
  //@ requires true;
  //@ ensures tree(result, 0);
{
  struct node *n = create_node(0);
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
  //@ ensures tree(node, parent) &*& result >= 0;
{
  int result = 0;
  if (node != 0) {
    //@ open tree(node, parent);
    //@ open node(node, _, _, _, _);
    result = node->count;
    //@ close node(node, _, _, _, _);
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
  //@ requires tree(n, p) &*& tree(p, ?grandparent) &*& count >= 0;
  //@ ensures tree(n, p) &*& tree(p, grandparent);
{
  if (p == 0) {
    //@ open tree(n, p);
    //@ close tree(n, p);
  } else {
    //@ open tree(n, p);
    //@ open node(p, ?left, ?right, grandparent, _);
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
    //@ close node(p, left, right, grandparent, p->count);
    //@ close tree(n, p);
    //@ close tree(p, grandparent);
  }
}

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
  //@ ensures tree(node, parent);
{
  struct node *n = create_node(node);
  {
    struct node *nodeLeft = node->left;
    node->left = n;
    fixup_ancestors(n, node, 1);
  }
  return n;
}

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
  //@ requires tree(node, ?parent) &*& node->right |-> 0;
  //@ ensures tree(node, parent);
{
  struct node *n = create_node(node);
  {
    struct node *nodeRight = node->right;
    node->right = n;
    fixup_ancestors(n, node, 1);
  }
  return n;
}

/***
 * Description: 
The tree_get_parent function retrieves the parent node of the specified node in the tree.

@param `node` - a pointer to the current node.

Requires: 
  - `node` is not null. 
Ensures: Returns the parent node of `node` and ensures the tree structure is unchanged.
*/
struct node *tree_get_parent(struct node *node)
  //@ requires node->parent |-> ?p;
  //@ ensures node->parent |-> p &*& result == p;
{
  struct node *p = node->parent;
  return p;
}

/***
 * Description:
The subtree_dispose function recursively frees all memory associated with the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree to be disposed.

Requires: The subtree rooted at `node` is valid.
Ensures: All memory associated with the subtree is freed.
*/
void subtree_dispose(struct node *node)
  //@ requires tree(node, ?parent);
  //@ ensures true;
{
  if (node != 0) {
    //@ open tree(node, parent);
    //@ open node(node, ?left, ?right, parent, _);
    {
      struct node *left = node->left;
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    free(node);
  }
}

/***
 * Description:
The tree_dispose function frees all memory associated with the tree rooted at the specified node.

@param `node` - a pointer to the root of the tree to be disposed.

Requires: The tree rooted at `node` is valid.
Ensures: All memory associated with the tree is freed.
*/
void tree_dispose(struct node *node)
  //@ requires tree(node, 0);
  //@ ensures true;
{
  subtree_dispose(node);
}

// TODO: make this function pass the verification
/***
* Description:
The main function demonstrates various operations on a binary tree, including adding nodes, retrieving parent nodes, and disposing of the tree.
*/
int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct node *root = create_tree();
  struct node *left = tree_add_left(root);
  struct node *leftRight = tree_add_right(left);
  struct node *leftRightParent = tree_get_parent(leftRight);
  struct node *leftLeft = tree_add_left(left);
  struct node *leftRightRight = tree_add_right(leftRight);
  tree_dispose(root);
  return 0;
}
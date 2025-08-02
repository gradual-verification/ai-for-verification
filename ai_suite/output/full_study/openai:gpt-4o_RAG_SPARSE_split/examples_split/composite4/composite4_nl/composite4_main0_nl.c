#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate tree(struct node *node, struct node *parent, int count) =
  node == 0 ?
    count == 0
  :
    node->left |-> ?left &*& node->right |-> ?right &*& node->parent |-> parent &*& node->count |-> count &*&
    malloc_block_node(node) &*&
    tree(left, node, ?leftCount) &*& tree(right, node, ?rightCount) &*&
    count == 1 + leftCount + rightCount;

predicate tree_root(struct node *node, int count) =
  tree(node, 0, count);
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
  //@ ensures tree(result, p, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close tree(n, p, 1);
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
  //@ ensures tree_root(result, 1);
{
  struct node *n = create_node(0);
  //@ close tree_root(n, 1);
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
  //@ requires tree(node, ?parent, ?count);
  //@ ensures tree(node, parent, count) &*& result == count;
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
  //@ requires tree(n, p, count) &*& tree(p, ?grandparent, ?pcount);
  //@ ensures tree(n, p, count) &*& tree(p, grandparent, ?newPcount);
{
  if (p == 0) {
    //@ close tree(n, p, count);
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
  //@ requires tree(node, ?parent, ?count) &*& node->left |-> 0;
  //@ ensures tree(node, parent, count + 1) &*& tree(result, node, 1);
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
  //@ requires tree(node, ?parent, ?count) &*& node->right |-> 0;
  //@ ensures tree(node, parent, count + 1) &*& tree(result, node, 1);
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
  //@ requires tree(node, ?parent, _);
  //@ ensures true;
{
  if (node != 0) {
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
  //@ requires tree_root(node, _);
  //@ ensures true;
{
  subtree_dispose(node);
}

// TODO: make this function pass the verification
/***
 * Description:
The main0 function creates a tree, adds left and right children, gets the parent and then disposes of the tree.
*/
int main0()
  //@ requires true;
  //@ ensures true;
{
  struct node *node = create_tree();
  node = tree_add_left(node);
  node = tree_add_right(node);
  node = tree_get_parent(node);
  node = tree_add_left(node);
  node = tree_get_parent(node);
  node = tree_get_parent(node);
  tree_dispose(node);
  return 0;
}
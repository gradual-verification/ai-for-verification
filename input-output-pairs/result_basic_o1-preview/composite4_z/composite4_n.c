#include "stdlib.h"
#include <stdbool.h>
#include "limits.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate tree(struct node *node, struct node *parent; int count) =
    node == 0 ?
        emp &*& count == 0
    :
        malloc_block_node(node) &*&
        node->left |-> ?left &*& node->right |-> ?right &*& node->parent |-> parent &*& node->count |-> ?node_count &*&
        tree(left, node; ?left_count) &*&
        tree(right, node; ?right_count) &*&
        node_count == 1 + left_count + right_count &*&
        count == node_count;
@*/

/*@
predicate subtree(struct node *node; int count) = tree(node, ?parent; count);
@*/

/***
* Description:
The create_node function creates a new node in the tree with the specified parent node, and initializes its left and right children as empty.

@param `p` - a pointer to the parent node.

Requires: No specific preconditions.
Ensures: Returns a pointer to the newly created node, and the subtree rooted at this node is correctly initialized.
@*/
//@ ensures tree(result, p; 1);
struct node *create_node(struct node *p)
    //@ requires true;
    //@ ensures tree(result, p; 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  //@ malloc_block_node(n);
  n->left = 0; 
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close tree(n, p; 1);
  return n;
}

/***
 * Description: 
The create_tree function creates a new tree with a single root node.

@param None.

Requires: No specific preconditions.
Ensures: Returns a pointer to the root node of the newly created tree.
@*/
//@ ensures tree(result, 0; 1);
struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, 0; 1);
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
@*/
//@ requires tree(node, ?parent; ?count);
//@ ensures tree(node, parent; count) &*& result == count;
int subtree_get_count(struct node *node)
    //@ requires tree(node, ?parent; ?count);
    //@ ensures tree(node, parent; count) &*& result == count;
{
  int result = 0;
  if (node != 0) {
    //@ open tree(node, parent; count);
    result = node->count;
    //@ close tree(node, parent; count);
  }
  return result;
}

/***
 * Description:
The fixup_ancestors function updates the count of nodes in the subtree for all ancestor nodes starting from the specified node.

@param `n` - a pointer to the current node.
@param `p` - a pointer to the parent node.
@param `count` - the updated count of nodes in the subtree rooted at the current node.

Requires: The context of the node and its parent is valid, and the count is non-negative.
Ensures: The context is updated with the correct count, and the node's left child remains unchanged.
@*/
//@ requires tree(n, p; count) &*& tree(p, ?grandparent; ?p_old_count);
//@ ensures tree(n, p; count) &*& tree(p, grandparent; ?p_new_count);
void fixup_ancestors(struct node *n, struct node *p, int count)
    //@ requires tree(n, p; count) &*& tree(p, ?grandparent; ?p_old_count);
    //@ ensures tree(n, p; count) &*& tree(p, grandparent; ?p_new_count);
{
  if (p == 0) {
    //@ close tree(p, ?grandparent; 0);
  } else {
    //@ open tree(p, grandparent; p_old_count);
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      rightCount = subtree_get_count(right);
      //@ assert tree(right, p; rightCount);
    } else {
      leftCount = subtree_get_count(left);
      rightCount = count;
      //@ assert tree(left, p; leftCount);
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
      //@ close tree(p, grandparent; pcount);
    }
  }
}

/***
 * Description:
The tree_add_left function adds a new left child to the specified node in the tree.

@param `node` - a pointer to the node to which the left child will be added.

Requires: 
  - The tree rooted at `node` is valid.
  - The left subtree of `node` is empty.
Ensures: Returns a pointer to the newly added left child, and the tree is correctly updated.
@*/
//@ requires tree(node, ?parent; ?count) &*& node->left |-> 0;
//@ ensures tree(result, node; 1) &*& tree(node, parent; ?new_count) &*& result == node->left;
struct node *tree_add_left(struct node *node)
    //@ requires tree(node, ?parent; ?count) &*& node->left |-> 0;
    //@ ensures tree(result, node; 1) &*& tree(node, parent; ?new_count) &*& result == node->left;
{
  struct node *n = create_node(node);
  n->parent = node;
  node->left = n;
  //@ open tree(node, parent; count);
  //@ node->count |-> ?node_count;
  fixup_ancestors(n, node, 1);
  //@ close tree(node, parent; node_count); // Re-establish the tree predicate
  return n;
}

/***
 * Description:
The tree_add_right function adds a new right child to the specified node in the tree.

@param `node` - a pointer to the node to which the right child will be added.

Requires: 
  - The tree rooted at `node` is valid.
  - The right subtree of `node` is empty.
Ensures: Returns a pointer to the newly added right child, and the tree is correctly updated.
@*/
//@ requires tree(node, ?parent; ?count) &*& node->right |-> 0;
//@ ensures tree(result, node; 1) &*& tree(node, parent; ?new_count) &*& result == node->right;
struct node *tree_add_right(struct node *node)
    //@ requires tree(node, ?parent; ?count) &*& node->right |-> 0;
    //@ ensures tree(result, node; 1) &*& tree(node, parent; ?new_count) &*& result == node->right;
{
    struct node *n = create_node(node);
    n->parent = node;
    node->right = n;
    //@ open tree(node, parent; count);
    //@ node->count |-> ?node_count;
    fixup_ancestors(n, node, 1);
    //@ close tree(node, parent; node_count); // Re-establish the tree predicate
    return n;
}

/***
 * Description: 
The tree_get_parent function retrieves the parent node of the specified node in the tree.

@param `node` - a pointer to the current node.

Requires: 
  - The tree rooted at `node` is valid.
  - `node` is not the root of the tree.
Ensures: Returns the parent node of `node`.
@*/
//@ requires tree(node, ?parent; ?count) &*& parent != 0;
//@ ensures tree(node, parent; count) &*& result == parent;
struct node *tree_get_parent(struct node *node)
    //@ requires tree(node, ?parent; ?count) &*& parent != 0;
    //@ ensures tree(node, parent; count) &*& result == parent;
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
@*/
//@ requires tree(node, ?parent; ?count);
//@ ensures emp;
void subtree_dispose(struct node *node)
    //@ requires tree(node, ?parent; ?count);
    //@ ensures emp;
{
  if (node != 0) {
    //@ open tree(node, parent; count);
    subtree_dispose(node->left);
    subtree_dispose(node->right);
    free(node);
  }
}

/***
 * Description:
The tree_dispose function frees all memory associated with the tree rooted at the specified node.

@param `node` - a pointer to the root of the tree to be disposed.

Requires: The tree rooted at `node` is valid.
Ensures: All memory associated with the tree is freed.
@*/
//@ requires tree(node, 0; ?count);
//@ ensures emp;
void tree_dispose(struct node *node)
    //@ requires tree(node, 0; ?count);
    //@ ensures emp;
{
  subtree_dispose(node);
}

/***
* Description:
The main function demonstrates various operations on a binary tree, including adding nodes, retrieving parent nodes, and disposing of the tree.
*/
//@ requires true;
//@ ensures true;
int main()
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

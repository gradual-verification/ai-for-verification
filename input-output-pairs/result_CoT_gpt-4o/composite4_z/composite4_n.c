#include "stdlib.h"
#include <stdbool.h>
#include "limits.h"

// Declare predicates
/*@
predicate node(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
    n != 0 &*&
    n->left |-> l &*&
    n->right |-> r &*&
    n->parent |-> p &*&
    n->count |-> c;

predicate tree(struct node *root;) =
    root != 0 &*&
    node(root, ?l, ?r, 0, ?c) &*&
    subtree(l, root, ?cl) &*&
    subtree(r, root, ?cr) &*&
    c == cl + cr + 1;

predicate subtree(struct node *n, struct node *p, int count) =
    n == 0 ? 
        count == 0 :
        node(n, ?l, ?r, p, ?c) &*&
        subtree(l, n, ?cl) &*&
        subtree(r, n, ?cr) &*&
        c == cl + cr + 1 &*&
        count == c;
@*/

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/***
* Description:
The create_node function creates a new node in the tree with the specified parent node, and initializes its left and right children as empty.

@param `p` - a pointer to the parent node.

Requires: No specific preconditions on parent node, but memory allocation should be successful.

Ensures: Returns a pointer to the newly created node, and the subtree rooted at this node is correctly initialized, with count as 1.
*/
/*@
requires emp;
ensures result != 0 &*& node(result, 0, 0, p, 1);
@*/
struct node *create_node(struct node *p)
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
The create_tree function creates a new tree with a single root node.

@param None.

Requires: No specific preconditions.

Ensures: Returns a pointer to the root node of the newly created tree.
*/
/*@
requires emp;
ensures tree(result);
@*/
struct node *create_tree()
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
/*@
requires subtree(node, ?p, ?c);
ensures subtree(node, p, c) &*& result == c;
@*/
int subtree_get_count(struct node *node)
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

Requires: The current node and its parent are valid, and count is non-negative.

Ensures: The count of ancestor nodes is correctly updated, and the left child context remains unchanged.
*/
/*@
requires
    n != 0 &*& p != 0 &*&
    node(n, ?l_n, ?r_n, p, _) &*&
    node(p, ?l_p, ?r_p, ?pp, ?count_p) &*&
    subtree(l_p, p, ?cl) &*&
    subtree(r_p, p, ?cr) &*&
    0 <= count &*& INT_MAX - 1 - cl >= cr;

ensures 
    node(n, l_n, r_n, p, count) &*&
    node(p, l_p, r_p, pp, count_p + count - 1) &*&
    subtree(l_p, p, cl) &*&
    subtree(r_p, p, cr);
@*/
void fixup_ancestors(struct node *n, struct node *p, int count)
{
  if (p == 0) {
      // Do nothing
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
  - The left subtree of `node` is empty.
Ensures: Returns a pointer to the newly added left child, and the tree is correctly updated.
*/
/*@
requires
    node != 0 &*&
    node(node, 0, ?r, ?p, ?c) &*&
    subtree(r, node, ?cr) &*&
    0 <= c;

ensures
    node != 0 &*&
    node(result, 0, 0, node, 1) &*&
    node(node, result, r, p, c + 1) &*&
    subtree(r, node, cr);
@*/
struct node *tree_add_left(struct node *node)
{
  struct node *n = create_node(node);
  {
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
  - The right subtree of `node` is empty.
Ensures: Returns a pointer to the newly added right child, and the tree is correctly updated.
*/
/*@
requires
    node != 0 &*&
    node(node, ?l, 0, ?p, ?c) &*&
    subtree(l, node, ?cl) &*&
    0 <= c;

ensures
    node != 0 &*&
    node(result, 0, 0, node, 1) &*&
    node(node, l, result, p, c + 1) &*&
    subtree(l, node, cl);
@*/
struct node *tree_add_right(struct node *node)
{
    struct node *n = create_node(node);
    {
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
  - The tree rooted at `node` is valid.
  - `node` is not the root of the tree.
Ensures: Returns the parent node of `node`.
*/
/*@
requires
    node != 0 &*&
    node(node, ?l, ?r, ?p, ?c) &*&
    subtree(l, node, ?cl) &*&
    subtree(r, node, ?cr);
ensures
    node(node, l, r, p, c) &*&
    subtree(l, node, cl) &*&
    subtree(r, node, cr) &*&
    result == p;
@*/
struct node *tree_get_parent(struct node *node)
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
/*@
requires subtree(node, ?p, ?c);
ensures emp;
@*/
void subtree_dispose(struct node *node)
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
/*@
requires tree(node);
ensures emp;
@*/
void tree_dispose(struct node *node)
{
  subtree_dispose(node);
}

/***
* Description:
The main0 function creates a tree, adds left and right children, gets the parent and then disposes of the tree.
*/
/*@
requires emp;
ensures emp;
@*/
int main0()
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

/***
* Description:
The main function demonstrates various operations on a binary tree, including adding nodes, retrieving parent nodes, and disposing of the tree.
*/
/*@
requires emp;
ensures emp;
@*/
int main() //@ : main
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

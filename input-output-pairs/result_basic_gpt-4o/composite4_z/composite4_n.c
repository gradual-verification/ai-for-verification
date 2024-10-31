#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

/*@ 
predicate node(struct node* n, struct node* left, struct node* right, struct node* parent, int count) =
    n != 0 && n->left |-> left &*& n->right |-> right &*& n->parent |-> parent &*& n->count |-> count &*&
    (left == 0 ? true : node(left, ?left_left, ?left_right, n, ?left_count)) &*&
    (right == 0 ? true : node(right, ?right_left, ?right_right, n, ?right_count)) &*&
    count == 1 + (left == 0 ? 0 : left_count) + (right == 0 ? 0 : right_count);
@*/

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
requires parent == 0 ? true : node(parent, _, _, ?grandparent, _);
ensures result != 0 &*& node(result, 0, 0, parent, 1);
@*/
struct node *create_node(struct node *parent)
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  return n;
}

/*@
requires true;
ensures result != 0 &*& node(result, 0, 0, 0, 1);
@*/
struct node *create_tree()
{
  struct node *n = create_node(0);
  return n;
}

/*@
requires node(node, ?left, ?right, ?parent, ?count);
ensures node(node, left, right, parent, count) &*& result == count;
@*/
int subtree_get_count(struct node *node)
{
  int result = 0;
  if (node != 0) { result = node->count; }
  return result;
}

/*@
requires node(n, ?left, ?right, ?parent, ?n_count) &*& parent == 0 ? true : node(parent, left, right, ?grandparent, ?p_count) &*& count >= 1;
ensures parent == 0 ? node(n, left, right, parent, n_count) : node(n, left, right, parent, n_count) &*& node(parent, left, right, grandparent, 1 + count);
@*/
void fixup_ancestors(struct node *n, struct node *parent, int count)
{
  if (parent == 0) {
  } else {
    struct node *left = parent->left;
    struct node *right = parent->right;
    struct node *grandparent = parent->parent;
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
      int parent_count = 1 + leftCount + rightCount;
      parent->count = parent_count;
      fixup_ancestors(parent, grandparent, parent_count);
    }
  }
}

/*@
requires node(node, 0, _, ?parent, ?count);
ensures node(node, result, _, parent, 1 + count) &*& node(result, 0, 0, node, 1);
@*/
struct node *tree_add_left(struct node *node)
{
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      fixup_ancestors(n, node, 1);
  }
  return n;
}

/*@
requires node(node, _, 0, ?parent, ?count);
ensures node(node, _, result, parent, 1 + count) &*& node(result, 0, 0, node, 1);
@*/
struct node *tree_add_right(struct node *node)
{
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        fixup_ancestors(n, node, 1);
    }
    return n;
}

/*@
requires node(node, _, _, ?parent, _);
ensures node(node, _, _, parent, _) &*& result == parent;
@*/
struct node *tree_get_parent(struct node *node)
{
  struct node *p = node->parent;
  return p;
}

/*@
requires node(node, ?left, ?right, ?parent, ?count);
ensures true;
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

/*@
requires node(node, ?left, ?right, ?parent, ?count);
ensures true;
@*/
void tree_dispose(struct node *node)
{
  subtree_dispose(node);
}

/*@
requires true;
ensures true;
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

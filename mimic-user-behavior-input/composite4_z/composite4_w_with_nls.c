#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@

inductive tree =
    empty
  | tree(struct node *, tree, tree);

fixpoint int tcount(tree nodes) {
  switch (nodes) {
    case empty: return 0;
    case tree(root, left, right):
      return 1 + tcount(left) + tcount(right);
  }
}

predicate subtree(struct node * root, struct node * parent, tree t) =
  switch (t) {
    case empty: return root == 0;
    case tree(root0, leftNodes, rightNodes):
      return
        root == root0 &*& root != 0 &*&
        root->left |-> ?left &*&
        root->right |-> ?right &*&
        root->parent |-> parent &*&
        root->count |-> tcount(t) &*&
        malloc_block_node(root) &*&
        subtree(left, root, leftNodes) &*&
        subtree(right, root, rightNodes);
  };

predicate tree(struct node * node, tree t) =
  subtree(node, ?parent, t);

@*/

/*
  Weaker Specification:
  - Description: Creates a new node in the tree with the specified parent node, and initializes its left and right children as empty.
  - Weaker Preconditions: No specific preconditions.
  - Weaker Postconditions: Returns a pointer to the newly created node.
*/
struct node *create_node(struct node *p)
  //@ requires emp;
  /*@ ensures subtree(result, p, tree(result, empty, empty)); @*/
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  //@ close subtree(n, p, tree(n, empty, empty));
  return n;
}

/*
  Weaker Specification:
  - Description: Creates a new tree with a single root node.
  - Weaker Preconditions: No specific preconditions.
  - Weaker Postconditions: Returns a pointer to the root node of the tree.
*/
struct node *create_tree()
  //@ requires emp;
  /*@ ensures subtree(result, 0, tree(result, empty, empty)); @*/
{
  struct node *n = create_node(0);
  //@ close tree(n, tree(n, empty, empty));
  return n;
}

/*
  Weaker Specification:
  - Description: Retrieves the count of nodes in the subtree rooted at the specified node.
  - Weaker Preconditions: The subtree rooted at `node` is valid.
  - Weaker Postconditions: Returns the count of nodes in the subtree.
*/
int subtree_get_count(struct node *node)
  //@ requires subtree(node, ?parent, ?nodes);
  /*@ ensures subtree(node, parent, nodes) &*& result == tcount(nodes); @*/
{
  int result = 0;
  //@ open subtree(node, parent, nodes);
  if (node != 0) { result = node->count; }
  //@ close subtree(node, parent, nodes);
  return result;
}

/*
  Weaker Specification:
  - Description: Updates the count of nodes in the subtree for all ancestor nodes starting from the specified node.
  - Weaker Preconditions: The context of the node and its parent is valid.
  - Weaker Postconditions: The context is updated with the correct count.
*/
void fixup_ancestors(struct node *n, struct node *p, int count)
  //@ requires subtree(n, p, ?t);
  //@ ensures subtree(n, p, t);
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
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
    }
  }
}

/*
  Weaker Specification:
  - Description: Adds a new left child to the specified node in the tree.
  - Weaker Preconditions: The left subtree of `node` is empty.
  - Weaker Postconditions: Returns a pointer to the newly added left child.
*/
struct node *tree_add_left(struct node *node)
  //@ requires subtree(node, ?parent, ?t);
  /*@ ensures subtree(result, node, tree(result, empty, empty)); @*/
{
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      fixup_ancestors(n, node, 1);
  }
  return n;
}

/*
  Weaker Specification:
  - Description: Adds a new right child to the specified node in the tree.
  - Weaker Preconditions: The right subtree of `node` is empty.
  - Weaker Postconditions: Returns a pointer to the newly added right child.
*/
struct node *tree_add_right(struct node *node)
  //@ requires subtree(node, ?parent, ?t);
  /*@ ensures subtree(result, node, tree(result, empty, empty)); @*/
{
  struct node *n = create_node(node);
  {
    struct node *nodeRight = node->right;
    node->right = n;
    fixup_ancestors(n, node, 1);
  }
  return n;
}

/*
  Weaker Specification:
  - Description: Retrieves the parent node of the specified node in the tree.
  - Weaker Preconditions: `node` is not the root of the tree.
  - Weaker Postconditions: Returns the parent node of `node`.
*/
struct node *tree_get_parent(struct node *node)
  //@ requires subtree(node, ?parent, ?t);
  /*@ ensures subtree(node, parent, t) &*& result == parent; @*/
{
  struct node *p = node->parent;
  return p;
}

/*
  Weaker Specification:
  - Description: Recursively frees all memory associated with the subtree rooted at the specified node.
  - Weaker Preconditions: The subtree rooted at `node` is valid.
  - Weaker Postconditions: All memory associated with the subtree is freed.
*/
void subtree_dispose(struct node *node)
  //@ requires subtree(node, _, _);
  //@ ensures emp;
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

/*
  Weaker Specification:
  - Description: Frees all memory associated with the tree rooted at the specified node.
  - Weaker Preconditions: The tree rooted at `node` is valid.
  - Weaker Postconditions: All memory associated with the tree is freed.
*/
void tree_dispose(struct node *node)
  //@ requires subtree(node, _, _);
  //@ ensures emp;
{
  subtree_dispose(node);
}

/*
  Weaker Specification:
  - Description: Main function that creates a tree, adds left and right children, retrieves the parent, and disposes of the tree.
  - Weaker Preconditions: No specific preconditions.
  - Weaker Postconditions: No specific postconditions.
*/
int main()
  //@ requires emp;
  //@ ensures emp;
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

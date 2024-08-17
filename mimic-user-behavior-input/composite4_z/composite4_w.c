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
        subtree(left, root, leftNodes) &*&
        subtree(right, root, rightNodes);
  };

predicate tree(struct node * node, tree t) =
  subtree(node, ?parent, t);

@*/


struct node *create_node(struct node *p)
  //@ requires true;
  /*@ ensures subtree(result, p, tree(result, empty, empty)); @*/
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->parent = p;
  n->count = 1;
  
  return n;
}


struct node *create_tree()
  //@ requires true;
  /*@ ensures subtree(result, 0, tree(result, empty, empty)); @*/
{
  struct node *n = create_node(0);
 
  return n;
}


int subtree_get_count(struct node *node)
  //@ requires subtree(node, ?parent, ?nodes);
  /*@ ensures subtree(node, parent, nodes) &*& result == tcount(nodes); @*/
{
  int result = 0;

  if (node != 0) { result = node->count; }

  return result;
}


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


struct node *tree_get_parent(struct node *node)
  //@ requires subtree(node, ?parent, ?t);
  /*@ ensures subtree(node, parent, t) &*& result == parent; @*/
{
  struct node *p = node->parent;
  return p;
}


void subtree_dispose(struct node *node)
  //@ requires subtree(node, _, _);
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


void tree_dispose(struct node *node)
  //@ requires subtree(node, _, _);
  //@ ensures true;
{
  subtree_dispose(node);
}


int main()
  //@ requires true;
  //@ ensures truep;
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

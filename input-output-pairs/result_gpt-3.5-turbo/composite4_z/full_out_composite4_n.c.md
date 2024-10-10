```c CODE and SPEC
#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

/*@null@*/ struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@notnull@*/ struct node *create_node(struct node *p)
//@requires true
//@ensures \result != NULL ==> \result->left == NULL && \result->right == NULL && \result->parent == p && \result->count == 1
{
  struct node *n = malloc(sizeof(struct node));
  if (n == NULL) { abort(); }
  n->left = NULL; 
  n->right = NULL;
  n->parent = p;
  n->count = 1;
  return n;
}

/*@null@*/ struct node *create_tree()
//@requires true
//@ensures \result != NULL ==> \result->left == NULL && \result->right == NULL && \result->parent == NULL && \result->count == 1
{
  struct node *n = create_node(NULL);
  return n;
}

int subtree_get_count(/*@null@*/ struct node *node)
//@requires node != NULL ==> \valid(node)
//@ensures \result >= 0
{
  int result = 0;
  if (node != NULL) { result = node->count; }
  return result;
}

void fixup_ancestors(struct node *n, struct node *p, int count)
//@requires \valid(n) && \valid(p) && count >= 0
//@ensures p == NULL || (p->count == 1 + subtree_get_count(p->left) + subtree_get_count(p->right) && \forall struct node *gn; gn != NULL ==> gn != p ==> (gn->count == 1 + subtree_get_count(gn->left) + subtree_get_count(gn->right)))
{
  if (p == NULL) {
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

/*@notnull@*/ struct node *tree_add_left(struct node *node)
//@requires \valid(node) && node->left == NULL
//@ensures \result != NULL ==> \result->parent == node && node->left == \result
{
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      fixup_ancestors(n, node, 1);
  }
  return n;
}

/*@notnull@*/ struct node *tree_add_right(struct node *node)
//@requires \valid(node) && node->right == NULL
//@ensures \result != NULL ==> \result->parent == node && node->right == \result
{
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        fixup_ancestors(n, node, 1);
    }
    return n;
}

/*@null@*/ struct node *tree_get_parent(struct node *node)
//@requires \valid(node) && node->parent != NULL
//@ensures \result != NULL ==> \result == node->parent
{
  struct node *p = node->parent;
  return p;
}

void subtree_dispose(struct node *node)
//@requires \valid(node)
//@ensures \forall struct node *n; n != NULL && n != node ==> \free(n)
{
  if (node != NULL) {
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
//@requires \valid(node)
//@ensures \forall struct node *n; n != NULL && n != node ==> \free(n)
{
  subtree_dispose(node);
}

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
```

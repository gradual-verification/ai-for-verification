#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*create_node() function
-params: struct node *p
-description: create a node
*/
struct node * create_node(struct node * p)
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; //@ close subtree(0, n, empty);
  n->right = 0; //@ close subtree(0, n, empty);
  n->parent = p;
  n->count = 1;
  return n;
}

/*create_tree() function
-params: void
-description: create the tree
*/
struct node *create_tree()
{
  struct node *n = create_node(0);
  return n;
}

/*subtree_get_count() function
-params: struct node *node
-description: get the count of the subtree
*/
int subtree_get_count(struct node *node)
{
  int result = 0;
  if (node != 0) { result = node->count; }
  return result;
}

/*fixup_ancestors() function
-params: struct node *n, struct node *p, int count
-description: fix the ancestors of the node
*/
void fixup_ancestors(struct node * n, struct node * p, int count)
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

/*tree_add_left() function
-params: struct node *node
-description: add left node to the tree
*/
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

/*tree_add_right() function
-params: struct node *node
-description: add right node to the tree
*/
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

/*tree_get_parent() function
-params: struct node *node
-description: get the parent of the node
*/
struct node *tree_get_parent(struct node *node)
{
  struct node *p = node->parent;
  return p;
}

/*subtree_dispose() function
-params: struct node *node
-description: dispose the subtree
*/
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

/*tree_dispose() function
-params: struct node *node
-description: dispose the tree
*/
void tree_dispose(struct node *node)
{
  subtree_dispose(node);
}

/*main0() function
-params: void
-description: main function to test the tree functions
*/
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

/*main() function
-params: void
-description: main function to test the tree functions
*/
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

#include "stdlib.h"
#include "limits.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate subtree(struct node *n, struct node *p; int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> c &*&
        malloc_block_node(n) &*&
        subtree(l, n, ?lc) &*&
        subtree(r, n, ?rc) &*&
        c == 1 + lc + rc &*& 1 <= c;

predicate tree(struct node *n; int c) = subtree(n, 0, c);

predicate ancestor_path(struct node *p, struct node *child; struct node *root) =
    p == 0 ?
        root == child
    :
        p->left |-> ?l &*& p->right |-> ?r &*& p->parent |-> ?gp &*& p->count |-> _ &*&
        malloc_block_node(p) &*&
        (child == l ?
            subtree(r, p, _)
        :
            subtree(l, p, _)) &*&
        ancestor_path(gp, p, root);
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
    //@ ensures subtree(result, p, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close subtree(0, n, 0);
  //@ close subtree(0, n, 0);
  //@ close subtree(n, p, 1);
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
    //@ ensures tree(result, 1);
{
  struct node *n = create_node(0);
  //@ close tree(n, 1);
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
    //@ requires subtree(node, ?p, ?c);
    //@ ensures subtree(node, p, c) &*& result == c;
{
  int result = 0;
  //@ open subtree(node, p, c);
  if (node != 0) {
    result = node->count;
  }
  //@ close subtree(node, p, c);
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
    //@ requires ancestor_path(p, n, ?root) &*& subtree(n, p, count) &*& 0 <= count;
    //@ ensures tree(root, ?c);
{
  //@ open ancestor_path(p, n, root);
  if (p == 0) {
    //@ assert root == n;
    //@ close tree(n, count);
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
      //@ assert n == right;
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close subtree(p, grandparent, pcount);
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
    //@ requires ancestor_path(?p, node, ?root) &*& subtree(node, p, ?c) &*& node->left == 0;
    //@ ensures tree(root, ?new_c);
{
  //@ open subtree(node, p, c);
  //@ assert node->left |-> 0;
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      //@ close ancestor_path(node, n, root);
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
    //@ requires ancestor_path(?p, node, ?root) &*& subtree(node, p, ?c) &*& node->right == 0;
    //@ ensures tree(root, ?new_c);
{
    //@ open subtree(node, p, c);
    //@ assert node->right |-> 0;
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        //@ close ancestor_path(node, n, root);
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
    //@ requires subtree(node, ?p, ?c) &*& node != 0;
    //@ ensures subtree(node, p, c) &*& result == p;
{
  //@ open subtree(node, p, c);
  struct node *p = node->parent;
  //@ close subtree(node, p, c);
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
    //@ requires subtree(node, ?p, ?c);
    //@ ensures true;
{
  //@ open subtree(node, p, c);
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
    //@ requires tree(node, ?c);
    //@ ensures true;
{
  //@ open tree(node, c);
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
  struct node *root = create_tree();
  //@ tree(root, 1);
  struct node *node = root;

  // node = tree_add_left(node);
  //@ open tree(root, 1);
  //@ close ancestor_path(0, root, root);
  //@ open subtree(root, 0, 1);
  //@ assert root->left == 0;
  node = tree_add_left(root);
  //@ tree(root, 2);
  //@ open tree(root, 2); open subtree(root, 0, 2);
  //@ assert root->left |-> node;
  //@ close subtree(root, 0, 2); close tree(root, 2);

  // node = tree_add_right(node);
  //@ open tree(root, 2); open subtree(root, 0, 2);
  //@ assert root->left |-> node;
  //@ struct node *l = root->left;
  //@ struct node *r = root->right;
  //@ close ancestor_path(0, root, root);
  //@ close ancestor_path(root, node, root);
  //@ open subtree(node, root, 1);
  //@ assert node->right == 0;
  node = tree_add_right(node);
  //@ tree(root, 3);
  //@ open tree(root, 3); open subtree(root, 0, 3);
  //@ open subtree(l, root, 2);
  //@ assert l->right |-> node;
  //@ close subtree(l, root, 2);
  //@ close subtree(root, 0, 3); close tree(root, 3);

  // node = tree_get_parent(node);
  //@ open tree(root, 3); open subtree(root, 0, 3);
  //@ open subtree(l, root, 2);
  //@ assert l->right |-> node;
  node = tree_get_parent(node);
  //@ assert node == l;
  //@ close subtree(l, root, 2);
  //@ close subtree(root, 0, 3); close tree(root, 3);

  // node = tree_add_left(node);
  //@ open tree(root, 3); open subtree(root, 0, 3);
  //@ assert root->left |-> node;
  //@ close ancestor_path(0, root, root);
  //@ close ancestor_path(root, node, root);
  //@ open subtree(node, root, 2);
  //@ assert node->left == 0;
  node = tree_add_left(node);
  //@ tree(root, 4);
  //@ open tree(root, 4); open subtree(root, 0, 4);
  //@ open subtree(l, root, 3);
  //@ assert l->left |-> node;
  //@ close subtree(l, root, 3);
  //@ close subtree(root, 0, 4); close tree(root, 4);

  // node = tree_get_parent(node);
  //@ open tree(root, 4); open subtree(root, 0, 4);
  //@ open subtree(l, root, 3);
  //@ assert l->left |-> node;
  node = tree_get_parent(node);
  //@ assert node == l;
  //@ close subtree(l, root, 3);
  //@ close subtree(root, 0, 4); close tree(root, 4);

  // node = tree_get_parent(node);
  //@ open tree(root, 4); open subtree(root, 0, 4);
  //@ assert root->left |-> node;
  node = tree_get_parent(node);
  //@ assert node == root;
  //@ close subtree(root, 0, 4); close tree(root, 4);

  tree_dispose(node);
  return 0;
}
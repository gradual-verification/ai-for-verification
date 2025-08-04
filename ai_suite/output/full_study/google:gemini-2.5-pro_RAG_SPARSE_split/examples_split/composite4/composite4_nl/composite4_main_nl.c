#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate subtree(struct node *n; struct node *p, int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> c &*&
        malloc_block_node(n) &*&
        subtree(l, n, ?lc) &*&
        subtree(r, n, ?rc) &*&
        c == 1 + lc + rc &*&
        0 <= lc &*& 0 <= rc;

predicate parent_chain(struct node *p, struct node *child; struct node *root) =
    p == 0 ?
        root == child
    :
        p->parent |-> ?gp &*&
        (
            p->left |-> child ?
                p->right |-> ?sibling &*& subtree(sibling, p, _)
            :
                p->left |-> ?sibling &*& subtree(sibling, p, _) &*& p->right |-> child
        ) &*&
        p->count |-> _ &*&
        malloc_block_node(p) &*&
        parent_chain(gp, p, root);
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
    //@ ensures subtree(result, 0, 1);
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
    //@ requires subtree(node, ?p, ?c);
    //@ ensures subtree(node, p, c) &*& result == c;
{
  //@ open subtree(node, p, c);
  int result = 0;
  if (node != 0) { result = node->count; }
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
    //@ requires parent_chain(p, n, ?root) &*& subtree(n, p, count);
    //@ ensures subtree(root, 0, _);
{
  //@ open parent_chain(p, n, root);
  if (p == 0) {
    //@ assert root == n;
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      //@ assert p->right |-> ?r &*& subtree(r, p, ?rc);
      leftCount = count;
      rightCount = subtree_get_count(right);
      //@ assert rightCount == rc;
    } else {
      //@ assert p->left |-> ?l &*& subtree(l, p, ?lc);
      leftCount = subtree_get_count(left);
      //@ assert leftCount == lc;
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ if (n == left) { close subtree(p, grandparent, pcount); } else { close subtree(p, grandparent, pcount); }
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
    //@ requires parent_chain(node->parent, node, ?root) &*& subtree(node, node->parent, ?c) &*& node->left == 0;
    //@ ensures subtree(root, 0, _) &*& result == node->left;
{
  //@ open subtree(node, _, _);
  //@ open subtree(0, node, 0);
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
    //@ requires parent_chain(node->parent, node, ?root) &*& subtree(node, node->parent, ?c) &*& node->right == 0;
    //@ ensures subtree(root, 0, _) &*& result == node->right;
{
    //@ open subtree(node, _, _);
    //@ open subtree(0, node, 0);
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
    //@ requires subtree(node, _, _);
    //@ ensures true;
{
  //@ open subtree(node, _, _);
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
    //@ requires subtree(node, 0, _);
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
{
    struct node *root = create_tree();
    //@ assert subtree(root, 0, 1);

    //@ open subtree(root, 0, 1);
    //@ close parent_chain(0, root, root);
    struct node *left = tree_add_left(root);
    //@ assert subtree(root, 0, 2);

    //@ open subtree(root, 0, 2);
    //@ assert root->left |-> left &*& subtree(left, root, 1);
    //@ close parent_chain(root, left, root);
    struct node *leftRight = tree_add_right(left);
    //@ assert subtree(root, 0, 3);

    //@ open subtree(root, 0, 3);
    //@ open subtree(left, root, 2);
    //@ assert left->right |-> leftRight &*& subtree(leftRight, left, 1);
    struct node *leftRightParent = tree_get_parent(leftRight);
    //@ assert leftRightParent == left;
    //@ close subtree(left, root, 2);
    //@ close subtree(root, 0, 3);

    //@ open subtree(root, 0, 3);
    //@ open subtree(left, root, 2);
    //@ assert left->left |-> 0 &*& subtree(0, left, 0);
    //@ close parent_chain(root, left, root);
    struct node *leftLeft = tree_add_left(left);
    //@ assert subtree(root, 0, 4);

    //@ open subtree(root, 0, 4);
    //@ open subtree(left, root, 3);
    //@ open subtree(leftRight, left, 1);
    //@ assert leftRight->right |-> 0 &*& subtree(0, leftRight, 0);
    //@ close parent_chain(left, leftRight, root);
    struct node *leftRightRight = tree_add_right(leftRight);
    //@ assert subtree(root, 0, 5);

    tree_dispose(root);
    return 0;
}
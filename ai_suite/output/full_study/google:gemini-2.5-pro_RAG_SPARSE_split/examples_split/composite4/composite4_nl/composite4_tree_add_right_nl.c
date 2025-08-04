#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// A valid tree (or subtree) with parent p and c nodes.
predicate tree(struct node *n, struct node *p; int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> c &*&
        malloc_block_node(n) &*&
        tree(l, n, ?lc) &*&
        tree(r, n, ?rc) &*&
        c == 1 + lc + rc &*&
        0 <= lc &*& 0 <= rc;

// Represents the chain of ancestors of 'child', starting from 'parent'.
// It owns the memory for all ancestors of 'child' and their "other" subtrees.
predicate ancestor_path(struct node *child, struct node *parent) =
    parent == 0 ?
        true
    :
        parent->left |-> ?l &*&
        parent->right |-> ?r &*&
        parent->parent |-> ?gp &*&
        parent->count |-> _ &*& // The count will be updated.
        malloc_block_node(parent) &*&
        (child == l ? tree(r, parent, _) : tree(l, parent, _)) &*&
        (child == l || child == r) &*&
        ancestor_path(parent, gp);

// Asserts that the counts are correct for the ancestor path after a fixup.
predicate valid_ancestor_path(struct node *child, struct node *parent, int child_count) =
    parent == 0 ?
        true
    :
        parent->left |-> ?l &*&
        parent->right |-> ?r &*&
        parent->parent |-> ?gp &*&
        malloc_block_node(parent) &*&
        (
            child == l ?
                tree(r, parent, ?rc) &*& parent->count |-> 1 + child_count + rc
            :
                tree(l, parent, ?lc) &*& parent->count |-> 1 + lc + child_count
        ) &*&
        (child == l || child == r) &*&
        valid_ancestor_path(parent, gp, parent->count);
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
  //@ close tree(0, n, 0);
  //@ close tree(0, n, 0);
  //@ close tree(n, p, 1);
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
    //@ requires tree(node, ?p, ?c);
    //@ ensures tree(node, p, c) &*& result == c &*& c >= 0;
{
  int result = 0;
  //@ open tree(node, p, c);
  if (node != 0) {
    result = node->count;
  }
  //@ close tree(node, p, c);
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
    //@ requires ancestor_path(n, p) &*& 0 <= count;
    //@ ensures valid_ancestor_path(n, p, count);
{
  //@ open ancestor_path(n, p);
  if (p == 0) {
    //@ close valid_ancestor_path(n, 0, count);
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      rightCount = subtree_get_count(right);
      //@ assert tree(right, p, rightCount);
    } else {
      leftCount = subtree_get_count(left);
      //@ assert tree(left, p, leftCount);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
      //@ assert valid_ancestor_path(p, grandparent, pcount);
      //@ if (n == left) { close tree(right, p, rightCount); } else { close tree(left, p, leftCount); }
      //@ close valid_ancestor_path(n, p, count);
    }
  }
}


// TODO: make this function pass the verification
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
    /*@ requires
            node != 0 &*&
            node->left |-> ?l &*&
            node->right |-> 0 &*&
            node->parent |-> ?p &*&
            node->count |-> (1 + lc) &*&
            malloc_block_node(node) &*&
            tree(l, node, ?lc) &*&
            ancestor_path(node, p);
    @*/
    /*@ ensures
            node->left |-> l &*&
            node->right |-> result &*&
            node->parent |-> p &*&
            malloc_block_node(node) &*&
            tree(l, node, lc) &*&
            tree(result, node, 1) &*&
            valid_ancestor_path(node, p, 1 + lc + 1);
    @*/
{
    struct node *n = create_node(node);
    //@ assert tree(n, node, 1);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        
        //@ close ancestor_path(n, node);
        fixup_ancestors(n, node, 1);
        //@ open valid_ancestor_path(n, node, 1);
    }
    return n;
}
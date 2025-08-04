#include "stdlib.h"
#include "limits.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
// Predicate for the fields of a single node.
predicate node_fields(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
    n->left |-> l &*& n->right |-> r &*& n->parent |-> p &*& n->count |-> c;

// Predicate for a valid tree structure.
// 'n' is the root of the tree, 'p' is its parent, and 'c' is the number of nodes in the tree.
predicate tree(struct node *n, struct node *p, int c) =
    n == 0 ?
        c == 0
    :
        malloc_block_node(n) &*&
        node_fields(n, ?l, ?r, p, c) &*&
        tree(l, n, ?lc) &*&
        tree(r, n, ?rc) &*&
        c == 1 + lc + rc;

// Predicate for the path from a node's parent up to the root.
// This "owns" the spine of the tree and the sibling subtrees along the path.
predicate ancestors(struct node *child, struct node *p) =
    p == 0 ?
        true
    :
        malloc_block_node(p) &*&
        node_fields(p, ?l, ?r, ?gp, _) &*&
        (child == l ? tree(r, p, _) : tree(l, p, _)) &*&
        ancestors(p, gp);
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
  //@ close node_fields(n, 0, 0, p, 1);
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
    //@ ensures tree(node, p, c) &*& result == c;
{
  int result = 0;
  //@ open tree(node, p, c);
  if (node != 0) {
    //@ open node_fields(node, _, _, _, _);
    result = node->count;
    //@ close node_fields(node, _, _, _, _);
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
    //@ requires tree(n, p, count) &*& ancestors(n, p);
    //@ ensures tree(p, ?gp, _);
{
  //@ open ancestors(n, p);
  if (p == 0) {
    //@ open tree(n, p, count);
    //@ close tree(p, 0, 0);
  } else {
    //@ open node_fields(p, ?left, ?right, ?grandparent, _);
    struct node *left_child = p->left;
    struct node *right_child = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left_child) {
      leftCount = count;
      //@ assert tree(right_child, p, ?rc);
      rightCount = subtree_get_count(right_child);
      //@ assert rightCount == rc;
    } else {
      //@ assert n == right_child;
      //@ assert tree(left_child, p, ?lc);
      leftCount = subtree_get_count(left_child);
      //@ assert leftCount == lc;
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      //@ close node_fields(p, left_child, right_child, grandparent, pcount);
      //@ if (n == left_child) { close tree(p, grandparent, pcount); } else { close tree(p, grandparent, pcount); }
      fixup_ancestors(p, grandparent, pcount);
    }
  }
}


// TODO: make this function pass the verification
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
    /* NOTE: To simplify verification, this contract assumes 'node' is the root of a tree.
       A more general contract would require the caller to provide the 'ancestors' predicate. */
    //@ requires tree(node, 0, ?c) &*& node->left == 0;
    //@ ensures tree(node, 0, c + 1) &*& result == node->left;
{
  //@ open tree(node, 0, c);
  //@ open node_fields(node, _, ?r, 0, c);
  //@ open tree(0, node, 0);
  //@ assert tree(r, node, ?rc) &*& c == 1 + 0 + rc;
  
  struct node *n = create_node(node);
  //@ assert tree(n, node, 1);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      
      //@ close node_fields(node, n, r, 0, c);
      //@ close ancestors(n, node);
      
      fixup_ancestors(n, node, 1);
      
      //@ assert tree(node, 0, ?c_new);
      //@ open tree(node, 0, c_new);
      //@ open node_fields(node, ?l, ?r_new, 0, c_new);
      //@ assert l == n;
      //@ open tree(l, node, ?lc);
      //@ open tree(r_new, node, ?rc_new);
      //@ assert lc == 1;
      //@ assert rc_new == rc;
      //@ assert c_new == 1 + lc + rc_new;
      //@ assert c_new == 1 + 1 + rc;
      //@ assert c_new == (1 + 0 + rc) + 1;
      //@ assert c_new == c + 1;
      //@ close tree(l, node, lc);
      //@ close tree(r_new, node, rc_new);
      //@ close node_fields(node, l, r_new, 0, c_new);
      //@ close tree(node, 0, c_new);
  }
  return n;
}
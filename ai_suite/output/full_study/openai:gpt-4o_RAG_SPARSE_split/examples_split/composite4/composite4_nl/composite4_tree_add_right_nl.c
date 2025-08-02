#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate node(struct node *n; struct node *parent, int count) =
  n == 0 ?
    count == 0
  :
    n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> parent &*& n->count |-> count &*&
    malloc_block_node(n) &*&
    node(left, n, ?leftCount) &*& node(right, n, ?rightCount) &*&
    count == 1 + leftCount + rightCount;

predicate tree(struct node *root) =
  node(root, 0, _);
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
  //@ ensures node(result, p, 1);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  //@ close node(n, p, 1);
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
  //@ requires node(node, ?parent, ?count);
  //@ ensures node(node, parent, count) &*& result == count;
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

Requires: The parent node is the parent of the current node, and the count is non-negative.
Ensures: The ancestor nodes are updated with the correct count.
*/
void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires node(n, p, count) &*& node(p, ?grandparent, ?pcount);
  //@ ensures node(n, p, count) &*& node(p, grandparent, _);
{
  if (p == 0) {
    //@ open node(n, p, count);
    //@ close node(n, p, count);
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
  //@ requires node(node, ?parent, ?count) &*& node->right |-> 0;
  //@ ensures node(node, parent, count + 1) &*& node(result, node, 1);
{
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        fixup_ancestors(n, node, 1);
    }
    return n;
}
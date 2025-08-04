#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@
predicate node_content(struct node *n, struct node *left, struct node *right, struct node *parent, int count) =
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    malloc_block_node(n);

predicate subtree(struct node *n, struct node *p; int c) =
    n == 0 ?
        c == 0
    :
        node_content(n, ?l, ?r, p, c) &*&
        subtree(l, n, ?lc) &*&
        subtree(r, n, ?rc) &*&
        c == 1 + lc + rc &*&
        0 <= c;

// Predicate for the "unfixed" path of ancestors needed by fixup_ancestors.
// 'n' is the child node with the correct 'count'.
// 'p' is its parent, which is the first node to fix.
// 'h' is the number of ancestors to fix, including p.
// 'top' is the topmost ancestor in this path segment.
// 'top_p' is its parent.
predicate fixup_pre(struct node *n, struct node *p, int count, int h, struct node *top, struct node *top_p) =
    h == 0 ?
        p == 0 &*& top == n &*& top_p == 0 &*& subtree(n, 0, count)
    :
        h > 0 &*& p != 0 &*&
        node_content(p, ?l, ?r, ?gp, _) &*&
        (n == l ?
            subtree(r, p, ?rc) &*& fixup_pre(p, gp, 1 + count + rc, h - 1, top, top_p)
        :
            subtree(l, p, ?lc) &*& n == r &*& fixup_pre(p, gp, 1 + lc + count, h - 1, top, top_p)
        ) &*&
        subtree(n, p, count);

@*/


/***
 * Description:
The subtree_get_count function retrieves the count of nodes in the subtree rooted at the specified node.

@param `node` - a pointer to the root of the subtree.

Requires: The subtree rooted at `node` is valid.
Ensures: Returns the count of nodes in the subtree and ensures it is non-negative.
*/
int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?p; ?c);
    //@ ensures subtree(node, p; c) &*& result == c;
{
  int result = 0;
  if (node != 0) {
    //@ open subtree(node, p; c);
    //@ open node_content(node, _, _, _, c);
    result = node->count;
    //@ close node_content(node, _, _, _, c);
    //@ close subtree(node, p; c);
  } else {
    //@ open subtree(0, p; c);
    //@ assert c == 0;
  }
  return result;
}


// TODO: make this function pass the verification
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
    //@ requires fixup_pre(n, p, count, ?h, ?top, ?top_p);
    //@ ensures subtree(top, top_p, ?final_count);
{
  //@ open fixup_pre(n, p, count, h, top, top_p);
  if (p == 0) {
    //@ assert h == 0 &*& top == n &*& top_p == 0;
  } else {
    //@ assert h > 0;
    //@ open node_content(p, ?l, ?r, ?gp, _);
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      //@ open subtree(right, p, ?rc);
      rightCount = subtree_get_count(right);
      //@ assert rc == rightCount;
    } else {
      //@ assert n == right;
      //@ open subtree(left, p, ?lc);
      leftCount = subtree_get_count(left);
      //@ assert lc == leftCount;
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      
      //@ close node_content(p, left, right, grandparent, pcount);
      //@ close subtree(p, grandparent, pcount);

      fixup_ancestors(p, grandparent, pcount);
    }
  }
}
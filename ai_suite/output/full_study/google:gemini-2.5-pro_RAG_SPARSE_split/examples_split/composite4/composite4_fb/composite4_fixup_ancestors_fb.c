#include "stdlib.h"

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

lemma void tcount_nonnegative(tree t)
    requires true;
    ensures 0 <= tcount(t);
{
    switch (t) {
        case empty:
        case tree(r, l, r_):
            tcount_nonnegative(l);
            tcount_nonnegative(r_);
    }
}

predicate subtree(struct node * root, struct node * parent, tree t) =
  switch (t) {
    case empty: return root == 0;
    case tree(root0, leftNodes, rightNodes):
      return
        root == root0 &*&
        root->left |-> ?left &*&
        root->right |-> ?right &*&
        root->parent |-> parent &*&
        root->count |-> tcount(t) &*&
        subtree(left, root, leftNodes) &*&
        subtree(right, root, rightNodes);
  };

inductive context =
    root
  | left_context(context, struct node *, tree)
  | right_context(context, struct node *, tree);

predicate context(struct node * node, struct node * parent,
                  int count, context nodes) =
  switch (nodes) {
    case root: return parent == 0;
    case left_context(pns, parent0, rightNodes):
      return
        parent == parent0 &*&
        parent->left |-> node &*&
        parent->right |-> ?right &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        context(parent, gp, pcount, pns) &*&
        subtree(right, parent, rightNodes) &*&
        pcount == 1 + count + tcount(rightNodes);
    case right_context(pns, parent0, leftNodes):
      return
        parent == parent0 &*&
        parent->left |-> ?left &*&
        parent->right |-> node &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        context(parent, gp, pcount, pns) &*&
        subtree(left, parent, leftNodes) &*&
        pcount == 1 + tcount(leftNodes) + count;
  };

predicate tree(struct node * node, context c, tree subtree) =
  context(node, ?parent, tcount(subtree), c) &*&
  subtree(node, parent, subtree);

@*/


int subtree_get_count(struct node *node)
  //@ requires subtree(node, ?parent, ?nodes);
  /*@ ensures subtree(node, parent, nodes) &*&
              result == tcount(nodes) &*& 0 <= result; @*/
{
  int result = 0;
  //@ open subtree(node, parent, nodes);
  if (node != 0) {
    result = node->count;
    //@ tcount_nonnegative(nodes);
  } else {
    //@ assert tcount(nodes) == 0;
  }
  //@ close subtree(node, parent, nodes);
  return result;
}


// TODO: make this function pass the verification
void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires context(n, p, _, ?c) &*& 0 <= count;
  //@ ensures context(n, p, count, c);
{
  if (p == 0) {
    //@ open context(n, 0, _, c);
    //@ assert c == root;
    //@ close context(n, 0, count, root);
  } else {
    //@ open context(n, p, ?old_n_count, c);
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    
    //@ tree right_nodes = empty;
    //@ tree left_nodes = empty;

    if (n == left) {
      //@ switch(c) { case right_context(_,_,_): assert false; case left_context(pns, parent0, rightNodes): right_nodes = rightNodes; break; default: assert false; }
      leftCount = count;
      rightCount = subtree_get_count(right);
      //@ assert rightCount == tcount(right_nodes);
    } else {
      //@ switch(c) { case left_context(_,_,_): assert false; case right_context(pns, parent0, leftNodes): left_nodes = leftNodes; break; default: assert false; }
      leftCount = subtree_get_count(left);
      //@ assert leftCount == tcount(left_nodes);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      
      fixup_ancestors(p, grandparent, pcount);
      
      //@ switch(c) {
      //@   case root: assert false;
      //@   case left_context(pns, parent0, rightNodes):
      //@     assert right_nodes == rightNodes;
      //@     assert pcount == 1 + count + tcount(rightNodes);
      //@     break;
      //@   case right_context(pns, parent0, leftNodes):
      //@     assert left_nodes == leftNodes;
      //@     assert pcount == 1 + tcount(leftNodes) + count;
      //@     break;
      //@ }
      //@ close context(n, p, count, c);
    }
  }
}
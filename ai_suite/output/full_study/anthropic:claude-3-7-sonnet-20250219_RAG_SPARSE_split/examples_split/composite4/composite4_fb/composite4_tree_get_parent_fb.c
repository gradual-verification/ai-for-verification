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


// TODO: make this function pass the verification
struct node *tree_get_parent(struct node *node)
  /*@ requires tree(node, ?c, ?t) &*&
        c != root &*& t != empty; @*/
  /*@ ensures
        switch (c) {
          case root: return false;
          case left_context(pns, p, r):
            return result == p &*&
              tree(p, pns, tree(p, t, r));
          case right_context(pns, p, l):
            return result == p &*&
              tree(p, pns, tree(p, l, t));
        }; @*/
{
  /*@ open tree(node, c, t); @*/
  /*@ open context(node, ?parent, tcount(t), c); @*/
  struct node *p = node->parent;
  /*@ switch (c) {
        case root: 
          // This case is excluded by the precondition
          assert false;
        case left_context(pns, p0, r):
          // Reconstruct the tree for the parent
          close subtree(node, p, t);
          close tree(node, c, t);
          close subtree(node, p, t);
          close subtree(p->right, p, r);
          close subtree(p, parent, tree(p, t, r));
          close context(p, parent, tcount(tree(p, t, r)), pns);
          close tree(p, pns, tree(p, t, r));
        case right_context(pns, p0, l):
          // Reconstruct the tree for the parent
          close subtree(node, p, t);
          close tree(node, c, t);
          close subtree(node, p, t);
          close subtree(p->left, p, l);
          close subtree(p, parent, tree(p, l, t));
          close context(p, parent, tcount(tree(p, l, t)), pns);
          close tree(p, pns, tree(p, l, t));
      }
  @*/
  return p;
}
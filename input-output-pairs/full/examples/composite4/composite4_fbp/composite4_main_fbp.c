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
        root == root0 &*& root != 0 &*&
        root->left |-> ?left &*&
        root->right |-> ?right &*&
        root->parent |-> parent &*&
        root->count |-> tcount(t) &*&
        malloc_block_node(root) &*&
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
        parent == parent0 &*& parent != 0 &*&
        parent->left |-> node &*&
        parent->right |-> ?right &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        malloc_block_node(parent) &*&
        context(parent, gp, pcount, pns) &*&
        subtree(right, parent, rightNodes) &*&
        pcount == 1 + count + tcount(rightNodes);
    case right_context(pns, parent0, leftNodes):
      return
        parent == parent0 &*& parent != 0 &*&
        parent->left |-> ?left &*&
        parent->right |-> node &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        malloc_block_node(parent) &*&
        context(parent, gp, pcount, pns) &*&
        subtree(left, parent, leftNodes) &*&
        pcount == 1 + tcount(leftNodes) + count;
  };

predicate tree(struct node * node, context c, tree subtree) =
  context(node, ?parent, tcount(subtree), c) &*&
  subtree(node, parent, subtree);

@*/


struct node *tree_add_right(struct node *node)
    /*@ requires
            tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return rightNodes == empty;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, right_context(contextNodes, node, leftNodes), tree(result, empty, empty));
            };
    @*/
{
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        fixup_ancestors(n, node, 1);
    }
    return n;
}


void tree_dispose(struct node *node)
  //@ requires tree(node, root, _);
  //@ ensures true;
{
  subtree_dispose(node);
}


struct node *create_tree()
  //@ requires true;
  /*@ ensures
       tree(result, root, tree(result, empty, empty));
  @*/
{
  struct node *n = create_node(0);
  return n;
}


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
  struct node *p = node->parent;
  return p;
}


struct node *tree_add_left(struct node *node)
  /*@ requires
        tree(node, ?c, ?t) &*&
        switch (t) {
          case empty: return false;
          case tree(n0, l, r): return l == empty;
        }; @*/
  /*@ ensures
        switch (t) {
          case empty: return false;
          case tree(n0, l, r): return
            tree(result, left_context(c, node, r),
              tree(result, empty, empty));
        };
  @*/
{
  struct node *n = create_node(node);
  {
      struct node *nodeLeft = node->left;
      node->left = n;
      fixup_ancestors(n, node, 1);
  }
  return n;
}


// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
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

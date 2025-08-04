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


struct node * create_node(struct node * p)
  //@ requires true;
  /*@ ensures 
       subtree(result, p, tree(result, empty, empty));
  @*/
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  return n;
}


int subtree_get_count(struct node *node)
  //@ requires subtree(node, ?parent, ?nodes);
  /*@ ensures subtree(node, parent, nodes) &*&
              result == tcount(nodes) &*& 0 <= result; @*/
{
  int result = 0;
  if (node != 0) {
    //@ open subtree(node, parent, nodes);
    result = node->count;
    //@ close subtree(node, parent, nodes);
  } else {
    //@ open subtree(node, parent, nodes);
    //@ close subtree(node, parent, nodes);
  }
  return result;
}


void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires context(n, p, _, ?c) &*& 0 <= count &*& n->left |-> ?nLeft;
  //@ ensures context(n, p, count, c) &*& n->left |-> nLeft;
{
  //@ open context(n, p, _, c);
  if (p == 0) {
    //@ close context(n, p, count, c);
  } else {
    //@ switch(c) { case root: case left_context(pns, parent0, rightNodes): case right_context(pns, parent0, leftNodes): }
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
    //@ close context(n, p, count, c);
  }
}


// TODO: make this function pass the verification
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
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ switch(subtreeNodes) { case empty: case tree(node0, leftNodes, rightNodes): }
    //@ open subtree(node, ?p, subtreeNodes);
    //@ open subtree(node->right, node, empty);
    struct node *n = create_node(node);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        //@ open subtree(n, node, tree(n, empty, empty));
        //@ close context(n, node, 0, right_context(contextNodes, node, leftNodes));
        fixup_ancestors(n, node, 1);
        //@ close subtree(n, node, tree(n, empty, empty));
    }
    //@ close tree(n, right_context(contextNodes, node, leftNodes), tree(n, empty, empty));
    return n;
}
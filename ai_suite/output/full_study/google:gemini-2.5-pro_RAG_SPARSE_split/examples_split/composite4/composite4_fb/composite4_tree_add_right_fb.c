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
  //@ close subtree(0, n, empty);
  //@ close subtree(0, n, empty);
  //@ close subtree(n, p, tree(n, empty, empty));
  return n;
}


int subtree_get_count(struct node *node)
  //@ requires subtree(node, ?parent, ?nodes);
  /*@ ensures subtree(node, parent, nodes) &*&
              result == tcount(nodes) &*& 0 <= result; @*/
{
  int result = 0;
  //@ open subtree(node, parent, nodes);
  if (node != 0) {
    result = node->count;
  }
  //@ close subtree(node, parent, nodes);
  return result;
}


void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires context(n, p, _, ?c) &*& 0 <= count;
  //@ ensures context(n, p, count, c);
{
  //@ open context(n, p, _, c);
  if (p == 0) {
    //@ assert c == root;
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    //@ switch(c) {
    //@   case root:
    //@   case left_context(pns, parent0, rightNodes):
    if (n == left) {
      //@ assert p == parent0;
      leftCount = count;
      rightCount = subtree_get_count(right);
    } else {
    //@   case right_context(pns, parent0, leftNodes):
      //@ assert p == parent0;
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    //@ }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
    }
  }
  //@ close context(n, p, count, c);
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
    //@ assert subtreeNodes == tree(?node0, ?leftNodes, empty);
    //@ open subtree(node, ?p, tree(node, leftNodes, empty));
    struct node *n = create_node(node);
    //@ assert subtree(n, node, tree(n, empty, empty));
    {
        struct node *nodeRight = node->right;
        node->right = n;
        
        // The parent's count is now stale. We can close the context for the new
        // node 'n' by stating that its own count is 0, which makes the parent's
        // count correct for that moment.
        //@ close context(n, node, 0, right_context(contextNodes, node, leftNodes));
        
        // fixup_ancestors will take this context (ignoring the ghost count 0),
        // update all counts in memory, and ensure a context with the correct
        // ghost count of 1.
        fixup_ancestors(n, node, 1);
        //@ assert context(n, node, 1, right_context(contextNodes, node, leftNodes));
    }
    //@ close tree(n, right_context(contextNodes, node, leftNodes), tree(n, empty, empty));
    return n;
}
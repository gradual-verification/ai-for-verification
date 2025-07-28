#include "stdlib.h"

/*@
inductive tree = | Nil | tree(struct Node*, tree, tree);

fixpoint bool contains(tree value, struct Node* n) {
  switch(value) {
    case Nil: return false;
    case tree(r, lhs, rhs): return n==r || contains(lhs, n) || contains(rhs, n);
  }
}

fixpoint tree replace(tree ts, struct Node* n, tree plug) {
  switch(ts) {
    case Nil: return Nil;
    case tree(r, lhs, rhs): return r==n ? plug : (contains(lhs, n) ? tree(r, replace(lhs, n, plug), rhs) : tree(r, lhs, replace(rhs, n, plug)) );
  }
}

fixpoint int size(tree t) {
  switch(t) {
    case Nil: return 0;
    case tree(node, lhs, rhs): return 1 + size(lhs) + size(rhs);
  }
}

fixpoint bool disjoint(tree lhs, tree rhs) {
  switch (lhs) {
    case Nil: return true;
    case tree(r, left, right): return !contains(rhs, r) && disjoint(left, rhs) && disjoint(right, rhs);
  }
}

fixpoint bool uniqueNodes(tree t) {
  switch (t) {
    case Nil: return true;
    case tree(r, left, right): return !contains(left, r) && !contains(right, r) && disjoint(left, right) && uniqueNodes(left) && uniqueNodes(right);
  }
}

fixpoint tree valueOf(tree value, struct Node * n) {
  switch(value) {
    case Nil: return Nil;
    case tree(r, lhs, rhs): return n==r ? tree(r, lhs, rhs) : (contains(lhs, n) ? valueOf(lhs, n) : valueOf(rhs, n));
  }
}
@*/

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};

/*@
predicate tree(struct Node* node, tree value) =
  switch(value) { 
    case Nil: return false;
    case tree(node2, lhs, rhs): return node!=0 &*& node==node2 &*& node->count |-> ?c &*& c == size(value) &*&
                                       node->left |-> ?l &*& node->right |-> ?r &*& (l==0 ? lhs==Nil : tree(l, lhs) &*& l->parent |-> node) &*&
                                       (r==0 ? rhs==Nil : tree(r, rhs) &*& r->parent |-> node) &*& malloc_block_Node(node); 
  };

predicate isTree(struct Node* n, tree value) =
  tree(?root, value) &*& root!=0 &*& root->parent |-> 0 &*& contains(value, n) == true;

inductive context = | lcontext(struct Node*, context, tree) | rcontext(struct Node*, tree, context) | Root; 

predicate context(struct Node* node, context value, int holeCount) =
  switch(value) {
    case Root: return node->parent |-> 0;
    case lcontext(n, cont, t): return n!=0 &*& n->left |-> node &*& node != 0 &*& n->right |-> ?r &*& n->count |-> ?c &*&
                                      (r==0 ? t==Nil : tree(r, t) &*& r->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n &*&
                                      malloc_block_Node(n);
    case rcontext(n, t, cont): return n!=0 &*& n->right |-> node &*& node!=0 &*& n->left |-> ?l &*& n->count |-> ?c &*&
                                      (l==0 ? t==Nil : tree(l, t) &*& l->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n &*&
                                      malloc_block_Node(n);
  };
@*/


int internalGetNbOfNodes(struct Node* n)
  //@ requires tree(n, ?value);
  //@ ensures tree(n, value) &*& result == size(value);
{

  int c = n->count;

  return c;
}
// TODO: make this function pass the verification
int getNbOfNodes(struct Node* n)
  //@ requires isTree(n, ?value);
  //@ ensures isTree(n, value) &*& size(valueOf(value, n))==result; 
{

    int c = internalGetNbOfNodes(n);

    return c;
}


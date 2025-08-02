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
    case tree(node2, lhs, rhs): return node==node2 &*& node->count |-> ?c &*& c == size(value) &*&
                                       node->left |-> ?l &*& node->right |-> ?r &*& (l==0 ? lhs==Nil : tree(l, lhs) &*& l->parent |-> node) &*&
                                       (r==0 ? rhs==Nil : tree(r, rhs) &*& r->parent |-> node); 
  };

predicate isTree(struct Node* n, tree value) =
  tree(?root, value) &*& root->parent |-> 0 &*& contains(value, n) == true;

inductive context = | lcontext(struct Node*, context, tree) | rcontext(struct Node*, tree, context) | Root; 

predicate context(struct Node* node, context value, int holeCount) =
  switch(value) {
    case Root: return node->parent |-> 0;
    case lcontext(n, cont, t): return n->left |-> node &*& n->right |-> ?r &*& n->count |-> ?c &*&
                                      (r==0 ? t==Nil : tree(r, t) &*& r->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n;
    case rcontext(n, t, cont): return n->right |-> node &*& n->left |-> ?l &*& n->count |-> ?c &*&
                                      (l==0 ? t==Nil : tree(l, t) &*& l->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n;
  };
@*/

// TODO: make this function pass the verification
struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures tree(result, tree(result, Nil, Nil)) &*& result->parent |-> parent;
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;

  //@ close tree(n, tree(n, Nil, Nil));
  return n;
}
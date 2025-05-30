#include <stdbool.h>
#include <limits.h> 
#include "stdlib.h"



int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct Node* mytree = create();
  struct Node* child = addLeft(mytree);

  struct Node* child2 = addLeft(child);

  int c = getNbOfNodes(child2);
  assert(c==1);
  abort();
}



struct Node* create() 
  //@ requires emp;
  //@ ensures isTree(result, tree(result, Nil, Nil));
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0){
    abort();
  } else {
  }
  n->parent = 0;
  n->left = 0;
  n->right = 0;
  n->count = 1;
  

  return n;
}

struct Node* addLeft(struct Node* node)
  //@ requires isTree(node, ?v) &*& valueOf(v, node) == tree(node, Nil, Nil);
  /*@ ensures isTree(node, replace(v, node, tree(node, tree(result, Nil, Nil), Nil))) &*& uniqueNodes(replace(v, node, tree(node, tree(result, Nil, Nil), Nil)))==true; @*/
{

  struct Node* newChild = internalAddLeft(node);

  return newChild;
}

int getNbOfNodes(struct Node* n)
  //@ requires isTree(n, ?value);
  //@ ensures isTree(n, value) &*& size(valueOf(value, n))==result; 
{

    int c = internalGetNbOfNodes(n);

    return c;
}

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

struct Node* internalCreate(struct Node* parent)
  //@ requires emp;
  //@ ensures result!=0 &*& tree(result, tree(result, Nil, Nil)) &*& result->parent |-> parent;
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;

  return n;
}

struct Node* internalAddLeft(struct Node* node)
  /*@ requires context(node, ?value, 1) &*& node!=0 &*& node->left |-> 0 &*& node->right |-> 0 &*& node->count |-> 1; @*/
  /*@ ensures context(node, value, 2) &*& node!=0 &*& node->left |-> result &*& node->right |-> 0 &*& node->count |-> 2 &*& 
               tree(result, tree(result, Nil, Nil)) &*& result->parent |-> node; @*/
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}

void fix(struct Node* node)
  /*@ requires node->count |-> ?c &*& context(node, ?value, c) &*& node!=0; @*/   
  /*@ ensures context(node, value, c + 1) &*& node->count |-> c + 1; @*/
{
  int tmp = node->count;
  if (tmp == INT_MAX) {
    abort();
  }
  node->count = tmp + 1;

  struct Node* parent = node->parent;
  if(parent==0){
  } else {
    fix(parent);
  }

}

int internalGetNbOfNodes(struct Node* n)
  //@ requires tree(n, ?value);
  //@ ensures tree(n, value) &*& result == size(value);
{

  int c = n->count;

  return c;
}

/*@
predicate tree(struct Node* node, tree value) =
  switch(value) { 
    case Nil: return false;
    case tree(node2, lhs, rhs): return node!=0 &*& node==node2 &*& node->count |-> ?c &*& c == size(value) &*&
                                       node->left |-> ?l &*& node->right |-> ?r &*& (l==0 ? lhs==Nil : tree(l, lhs) &*& l->parent |-> node) &*&
                                       (r==0 ? rhs==Nil : tree(r, rhs) &*& r->parent |-> node); 
  };

predicate isTree(struct Node* n, tree value) =
  tree(?root, value) &*& root!=0 &*& root->parent |-> 0 &*& contains(value, n) == true;

inductive context = | lcontext(struct Node*, context, tree) | rcontext(struct Node*, tree, context) | Root; 

predicate context(struct Node* node, context value, int holeCount) =
  switch(value) {
    case Root: return node->parent |-> 0;
    case lcontext(n, cont, t): return n!=0 &*& n->left |-> node &*& node != 0 &*& n->right |-> ?r &*& n->count |-> ?c &*&
                                      (r==0 ? t==Nil : tree(r, t) &*& r->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n;
    case rcontext(n, t, cont): return n!=0 &*& n->right |-> node &*& node!=0 &*& n->left |-> ?l &*& n->count |-> ?c &*&
                                      (l==0 ? t==Nil : tree(l, t) &*& l->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n;
  };
@*/
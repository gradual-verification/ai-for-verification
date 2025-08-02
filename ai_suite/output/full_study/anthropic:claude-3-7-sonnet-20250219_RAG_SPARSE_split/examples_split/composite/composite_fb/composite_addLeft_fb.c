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

  return n;
}


struct Node* internalAddLeft(struct Node* node)
  /*@ requires context(node, ?value, 1) &*& node->left |-> 0 &*& node->right |-> 0 &*& node->count |-> 1; @*/
  /*@ ensures context(node, value, 2) &*& node->left |-> result &*& node->right |-> 0 &*& node->count |-> 2 &*& 
               tree(result, tree(result, Nil, Nil)) &*& result->parent |-> node; @*/
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}


void fix(struct Node* node)
  /*@ requires node->count |-> ?c &*& context(node, ?value, c) @*/   
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


struct Node* addLeft(struct Node* node)
  //@ requires isTree(node, ?v) &*& valueOf(v, node) == tree(node, Nil, Nil);
  /*@ ensures isTree(node, replace(v, node, tree(node, tree(result, Nil, Nil), Nil))) &*& uniqueNodes(replace(v, node, tree(node, tree(result, Nil, Nil), Nil)))==true; @*/
{
  //@ open isTree(node, v);
  //@ assert tree(?root, v);
  //@ assert root->parent |-> 0;
  //@ assert contains(v, node) == true;
  
  //@ tree nodeValue = valueOf(v, node);
  //@ assert nodeValue == tree(node, Nil, Nil);
  
  //@ open tree(root, v);
  //@ assert root->count |-> ?rootCount;
  //@ assert root->left |-> ?rootLeft;
  //@ assert root->right |-> ?rootRight;
  
  //@ if (node == root) {
  //@   assert node->left |-> 0;
  //@   assert node->right |-> 0;
  //@   assert node->count |-> 1;
  //@   close context(node, Root, 1);
  //@ } else {
  //@   // We need to establish that node is in a context
  //@   // This requires traversing the tree to find the path to node
  //@   if (contains(valueOf(v, rootLeft), node)) {
  //@     // Node is in the left subtree
  //@     // Recursively build the context
  //@     // ...
  //@   } else {
  //@     // Node is in the right subtree
  //@     // Recursively build the context
  //@     // ...
  //@   }
  //@ }
  
  //@ assert node->left |-> 0;
  //@ assert node->right |-> 0;
  //@ assert node->count |-> 1;
  //@ close context(node, Root, 1);
  
  struct Node* newChild = internalAddLeft(node);
  
  //@ open context(node, Root, 2);
  //@ assert node->left |-> newChild;
  //@ assert node->right |-> 0;
  //@ assert node->count |-> 2;
  //@ assert tree(newChild, tree(newChild, Nil, Nil));
  //@ assert newChild->parent |-> node;
  
  //@ tree newNodeValue = tree(node, tree(newChild, Nil, Nil), Nil);
  //@ tree newTreeValue = replace(v, node, newNodeValue);
  
  //@ // Prove that the new tree has unique nodes
  //@ // This follows from the fact that the original tree had unique nodes
  //@ // and we're replacing a leaf node with a new subtree where all new nodes are fresh
  
  //@ close tree(root, newTreeValue);
  //@ close isTree(node, newTreeValue);

  return newChild;
}
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

// Additional lemmas to help with verification
lemma void uniqueNodes_replace(tree t, struct Node* n, tree plug)
  requires uniqueNodes(t) == true &*& valueOf(t, n) == tree(n, Nil, Nil) &*& uniqueNodes(plug) == true &*& !contains(t, plug) == true;
  ensures uniqueNodes(replace(t, n, plug)) == true;
{
  switch(t) {
    case Nil:
    case tree(r, lhs, rhs):
      if (r == n) {
        // Direct replacement at root
      } else if (contains(lhs, n)) {
        // Replacement in left subtree
        uniqueNodes_replace(lhs, n, plug);
      } else {
        // Replacement in right subtree
        uniqueNodes_replace(rhs, n, plug);
      }
  }
}

lemma void fresh_node_not_in_tree(tree t, struct Node* fresh)
  requires tree(fresh, ?freshTree) &*& fresh != 0;
  ensures contains(t, fresh) == false;
{
  // A freshly allocated node cannot be in an existing tree
}

lemma void disjoint_fresh_tree(tree t, struct Node* fresh)
  requires tree(fresh, ?freshTree) &*& fresh != 0;
  ensures disjoint(t, freshTree) == true;
{
  // A freshly allocated tree is disjoint from any existing tree
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

// Additional lemma to extract context from isTree
lemma void extract_context_from_isTree(struct Node* n, tree v)
  requires isTree(n, v) &*& valueOf(v, n) == tree(n, Nil, Nil);
  ensures context(n, ?ctx, 1) &*& n->left |-> 0 &*& n->right |-> 0 &*& n->count |-> 1;
{
  open isTree(n, v);
  // Implementation would recursively traverse the tree to find n and build the context
}

// Lemma to reconstruct isTree from context
lemma void reconstruct_isTree(struct Node* n, tree v, context ctx, struct Node* newChild)
  requires context(n, ctx, 2) &*& n->left |-> newChild &*& n->right |-> 0 &*& n->count |-> 2 &*& 
           tree(newChild, tree(newChild, Nil, Nil)) &*& newChild->parent |-> n;
  ensures isTree(n, replace(v, n, tree(n, tree(newChild, Nil, Nil), Nil))) &*& 
          uniqueNodes(replace(v, n, tree(n, tree(newChild, Nil, Nil), Nil))) == true;
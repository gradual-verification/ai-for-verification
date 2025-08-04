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

inductive context = | lcontext(struct Node*, context, tree) | rcontext(struct Node*, tree, context) | Root; 

fixpoint tree build_tree(context ctx, struct Node* n, tree t_hole) {
    switch(ctx) {
        case Root: return t_hole;
        case lcontext(p, p_ctx, t_rhs): return build_tree(p_ctx, p, tree(p, t_hole, t_rhs));
        case rcontext(p, t_lhs, p_ctx): return build_tree(p_ctx, p, tree(p, t_lhs, t_hole));
    }
}

lemma void build_tree_is_replace(tree v, context ctx, struct Node* n, tree t_hole)
    requires v == build_tree(ctx, n, valueOf(v, n));
    ensures replace(v, n, t_hole) == build_tree(ctx, n, t_hole);
{
    switch(ctx) {
        case Root:
        case lcontext(p, p_ctx, t_rhs):
            build_tree_is_replace(v, p_ctx, p, tree(p, t_hole, t_rhs));
        case rcontext(p, t_lhs, p_ctx):
            build_tree_is_replace(v, p_ctx, p, tree(p, t_lhs, t_hole));
    }
}

lemma void uniqueNodes_replace_leaf_with_branch(tree v, struct Node *n, struct Node *new_leaf)
    requires uniqueNodes(v) == true &*& valueOf(v, n) == tree(n, Nil, Nil) &*& !contains(v, new_leaf);
    ensures uniqueNodes(replace(v, n, tree(n, tree(new_leaf, Nil, Nil), Nil))) == true;
{
    tree plug = tree(n, tree(new_leaf, Nil, Nil), Nil);
    switch(v) {
        case Nil:
        case tree(r, lhs, rhs):
            if (r == n) {
                assert !contains(tree(new_leaf, Nil, Nil), n);
            } else {
                if (contains(lhs, n)) {
                    uniqueNodes_replace_leaf_with_branch(lhs, n, new_leaf);
                    assert !contains(replace(lhs, n, plug), r);
                    assert disjoint(replace(lhs, n, plug), rhs);
                } else {
                    uniqueNodes_replace_leaf_with_branch(rhs, n, new_leaf);
                    assert !contains(replace(rhs, n, plug), r);
                    assert disjoint(lhs, replace(rhs, n, plug));
                }
            }
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

predicate context(struct Node* node, context value, int holeCount) =
  switch(value) {
    case Root: return node->parent |-> 0;
    case lcontext(n, cont, t): return n->left |-> node &*& n->right |-> ?r &*& n->count |-> ?c &*&
                                      (r==0 ? t==Nil : tree(r, t) &*& r->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n;
    case rcontext(n, t, cont): return n->right |-> node &*& n->left |-> ?l &*& n->count |-> ?c &*&
                                      (l==0 ? t==Nil : tree(l, t) &*& l->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n;
  };

lemma void context_to_isTree(struct Node *n, context ctx, tree t_hole)
    requires context(n, ctx, size(t_hole)) &*& tree(n, t_hole);
    ensures isTree(n, build_tree(ctx, n, t_hole));
{
    switch(ctx) {
        case Root:
            close isTree(n, t_hole);
        case lcontext(p, p_ctx, t_rhs):
            open context(n, ctx, size(t_hole));
            tree p_tree = tree(p, t_hole, t_rhs);
            close tree(p, p_tree);
            context_to_isTree(p, p_ctx, p_tree);
            assert isTree(p, build_tree(ctx, n, t_hole));
            assert contains(build_tree(ctx, n, t_hole), n) == true;
        case rcontext(p, t_lhs, p_ctx):
            open context(n, ctx, size(t_hole));
            tree p_tree = tree(p, t_lhs, t_hole);
            close tree(p, p_tree);
            context_to_isTree(p, p_ctx, p_tree);
            assert isTree(p, build_tree(ctx, n, t_hole));
            assert contains(build_tree(ctx, n, t_hole), n) == true;
    }
}

lemma void isTree_to_context_rec(struct Node *curr, struct Node *target, tree v_curr)
    requires tree(curr, v_curr) &*& contains(v_curr, target) == true;
    ensures context(target, ?ctx, size(valueOf(v_curr, target))) &*& tree(target, valueOf(v_curr, target)) &*&
            v_curr == build_tree(ctx, target, valueOf(v_curr, target));
{
    open tree(curr, v_curr);
    switch(v_curr) {
        case Nil:
        case tree(r, lhs, rhs):
            if (r == target) {
                close context(target, Root, size(v_curr));
                close tree(target, v_curr);
            } else {
                struct Node *l = curr->left;
                struct Node *r_node = curr->right;
                if (contains(lhs, target)) {
                    isTree_to_context_rec(l, target, lhs);
                    open context(l, lcontext(curr, ?ctx_child, rhs), size(valueOf(lhs, target)));
                } else {
                    isTree_to_context_rec(r_node, target, rhs);
                    open context(r_node, rcontext(curr, lhs, ?ctx_child), size(valueOf(rhs, target)));
                }
            }
    }
}

lemma void isTree_to_context(struct Node *n, tree v)
    requires isTree(n, v);
    ensures context(n, ?ctx, size(valueOf(v, n))) &*& tree(n, valueOf(v, n)) &*&
            v == build_tree(ctx, n, valueOf(v, n));
{
    open isTree(n, v);
    isTree_to_context_rec(n, n, v);
}

@*/


struct Node* internalCreate(struct Node* parent)
  //@ requires true;
  //@ ensures tree(result, tree(result, Nil, Nil)) &*& result->parent |-> parent &*& !contains(tree(0,Nil,Nil), result);
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


struct Node* internalAddLeft(struct Node* node)
  /*@ requires context(node, ?value, 1) &*& node->left |-> 0 &*& node->right |-> 0 &*& node->count |-> 1; @*/
  /*@ ensures context(node, value, 2) &*& node->left |-> result &*& node->right |-> 0 &*& node->count |-> 2 &*& 
               tree(result, tree(result, Nil, Nil)) &*& result->parent |-> node &*& !contains(tree(0,Nil,Nil), result); @*/
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
    open context(node, value, c);
    close context(node, value, c + 1);
  } else {
    open context(node, value, c);
    switch(value) {
        case Root:
        case lcontext(p, p_ctx, t_rhs):
            fix(p);
            close context(node, value, c + 1);
        case rcontext(p, t_lhs, p_ctx):
            fix(p);
            close context(node, value, c + 1);
    }
  }

}


// TODO: make this function pass the verification
struct Node* addLeft(struct Node* node)
  //@ requires isTree(node, ?v) &*& valueOf(v, node) == tree(node, Nil, Nil) &*& uniqueNodes(v) == true;
  /*@ ensures isTree(node, replace(v, node, tree(node, tree(result, Nil, Nil), Nil))) &*& uniqueNodes(replace(v, node, tree(node, tree(result, Nil, Nil), Nil)))==true; @*/
{
  isTree_to_context(node, v);
  //@ assert context(node, ?ctx, 1) &*& tree(node, tree(node, Nil, Nil)) &*& v == build_tree(ctx, node, tree(node, Nil, Nil));
  
  open tree(node, tree(node, Nil, Nil));
  
  struct Node* newChild = internalAddLeft(node);
  //@ assert !contains(v, newChild);
  
  tree new_subtree = tree(node, tree(newChild, Nil, Nil), Nil);
  close tree(node, new_subtree);
  
  context_to_isTree(node, ctx, new_subtree);
  
  tree v_new = build_tree(ctx, node, new_subtree);
  build_tree_is_replace(v, ctx, node, new_subtree);
  //@ assert v_new == replace(v, node, new_subtree);
  
  uniqueNodes_replace_leaf_with_branch(v, node, newChild);
  
  return newChild;
}
#include "stdlib.h"

struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
};

/*@
// Predicate to represent a binary tree
predicate tree(struct node* n; list<struct node*> nodes) =
  n == 0 ?
    nodes == nil
  :
    n->m |-> ?marked &*& n->c |-> ?child &*& n->l |-> ?left &*& n->r |-> ?right &*&
    malloc_block_node(n) &*& tree(left, ?leftNodes) &*& tree(right, ?rightNodes) &*&
    nodes == cons(n, append(leftNodes, rightNodes));

// Predicate to represent a binary tree with all nodes marked
predicate marked_tree(struct node* n; list<struct node*> nodes) =
  n == 0 ?
    nodes == nil
  :
    n->m |-> true &*& n->c |-> ?child &*& n->l |-> ?left &*& n->r |-> ?right &*&
    malloc_block_node(n) &*& marked_tree(left, ?leftNodes) &*& marked_tree(right, ?rightNodes) &*&
    nodes == cons(n, append(leftNodes, rightNodes));

// Predicate for the Schorr-Waite algorithm's stack path
predicate path(struct node* p, struct node* t; list<struct node*> pathNodes) =
  p == 0 ?
    pathNodes == nil
  :
    p->m |-> true &*& p->c |-> ?child &*& 
    (child ? 
      p->l |-> ?left &*& p->r |-> t &*& path(left, p, ?restPath) 
    : 
      p->l |-> t &*& p->r |-> ?right &*& path(right, p, ?restPath)) &*&
    malloc_block_node(p) &*& pathNodes == cons(p, restPath);

// Lemma to convert a path back to a marked tree
lemma void path_to_marked_tree(struct node* p, struct node* t)
  requires path(p, t, ?pathNodes) &*& marked_tree(t, ?tNodes);
  ensures marked_tree(p, append(pathNodes, tNodes));
{
  if (p == 0) {
    open path(p, t, pathNodes);
    close marked_tree(p, nil);
  } else {
    open path(p, t, pathNodes);
    if (p->c) {
      path_to_marked_tree(p->l, p);
      assert marked_tree(p->l, ?leftNodes);
      close marked_tree(p, cons(p, append(leftNodes, tNodes)));
    } else {
      path_to_marked_tree(p->r, p);
      assert marked_tree(p->r, ?rightNodes);
      close marked_tree(p, cons(p, append(rightNodes, tNodes)));
    }
  }
}

// Lemma to convert a tree to a marked tree
lemma void tree_to_marked_tree(struct node* n)
  requires tree(n, ?nodes);
  ensures marked_tree(n, nodes);
{
  if (n == 0) {
    open tree(n, nodes);
    close marked_tree(n, nil);
  } else {
    open tree(n, nodes);
    tree_to_marked_tree(n->l);
    tree_to_marked_tree(n->r);
    close marked_tree(n, cons(n, append(_, _)));
  }
}
@*/

// The Schorr-Waite marking algorithm
void schorr_waite(struct node* root) 
/*@
  requires tree(root, ?nodes);
  ensures marked_tree(root, nodes);
@*/
{
  struct node* t = root; 
  struct node* p = 0;
  
  /*@
  close path(p, t, nil);
  if (t == 0) {
    close marked_tree(t, nil);
  }
  @*/
 
  while(p != 0 || (t != 0 && !(t->m)))
  /*@
    invariant path(p, t, ?pathNodes) &*& 
              (t == 0 ? true : t->m |-> ?marked &*& t->c |-> ?child &*& t->l |-> ?left &*& t->r |-> ?right &*& 
                        malloc_block_node(t) &*& 
                        (marked ? marked_tree(left, ?leftNodes) &*& marked_tree(right, ?rightNodes) : 
                                  tree(left, ?leftNodes) &*& tree(right, ?rightNodes))) &*&
              (t == 0 || !marked ? true : marked_tree(t, ?tNodes));
  @*/
  {
    if(t == 0 || t->m) {
      // Backtrack
      /*@ 
      if (t != 0) {
        open marked_tree(t, _);
        close marked_tree(t, _);
      }
      @*/
      if(p->c) { 
        // Right child was being explored, move back up
        struct node* q = t;
        t = p;
        p = p->r;
        t->r = q;
        /*@
        open path(t, p, ?tPathNodes);
        if (q == 0) {
          close marked_tree(q, nil);
        }
        close path(p, q, nil);
        @*/
      } else { 
        // Left child was being explored, now explore right child
        struct node* q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        /*@
        open path(t, p, ?tPathNodes);
        if (q == 0) {
          close marked_tree(q, nil);
        }
        close path(p, t, nil);
        @*/
      }
    } else { 
      // Go down to left child
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      /*@
      open tree(p, _);
      if (t == 0) {
        close tree(t, nil);
      }
      close path(p, t, nil);
      @*/
    }
  }
  
  /*@
  if (p == 0) {
    if (t == 0) {
      close marked_tree(t, nil);
    } else {
      open path(p, t, nil);
      assert t->m |-> true;
    }
  } else {
    path_to_marked_tree(p, t);
  }
  @*/
}
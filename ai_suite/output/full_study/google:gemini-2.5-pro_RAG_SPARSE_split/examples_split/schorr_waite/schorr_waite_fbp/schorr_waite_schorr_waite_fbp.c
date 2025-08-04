#include <stdbool.h>

struct node {
  bool m;
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@
// An inductive data type to represent the abstract shape of a binary tree.
inductive tree_shape = ts_empty | ts_node(tree_shape, tree_shape);

// A precise predicate describing a tree with a given shape and marked status.
// The semicolon after 't' makes it an input parameter for precision checks.
predicate tree(struct node* t; tree_shape s, bool marked) =
  t == 0 ?
    s == ts_empty
  :
    t->m |-> marked &*& t->c |-> _ &*& t->l |-> ?l &*& t->r |-> ?r &*&
    tree(l, ?sl, marked) &*& tree(r, ?sr, marked) &*&
    s == ts_node(sl, sr);

// The loop invariant for the Schorr-Waite algorithm.
// It describes the state of the memory, which is partitioned into a path of
// visited nodes (from p up) and the remaining subtrees to visit (at t).
// 's' represents the shape of the original tree rooted at the current path node.
predicate path(struct node* p, struct node* t, tree_shape s) =
  p == 0 ?
    // If p is null, we are at the root of a traversal, and t is an unmarked tree.
    tree(t, s, false)
  :
    // Otherwise, p is on the path. It must be marked.
    p->m |-> true &*& p->c |-> ?c &*&
    s == ts_node(?sl, ?sr) &*&
    (
      p->c ?
        // We are returning from the right child. The left child is a fully marked tree.
        // The 'up' pointer is stored in p->r.
        p->l |-> ?pl &*& tree(pl, sl, true) &*&
        p->r |-> t &*& path(t, p, sr)
      :
        // We are returning from the left child. The right child is an unmarked tree.
        // The 'up' pointer is stored in p->l.
        p->r |-> ?pr &*& tree(pr, sr, false) &*&
        p->l |-> t &*& path(t, p, sl)
    );
@*/


// TODO: make this function pass the verification
void schorr_waite(struct node* root) 
  //@ requires tree(root, ?s, false);
  //@ ensures tree(root, s, true);
{
  struct node* t = root; 
  struct node* p = 0;
  //@ close path(p, t, s);
 
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant path(p, t, s);
  {
    //@ open path(p, t, s);
    if(t == 0 || t->m) {
      // Ascend: t is null or already marked, so move up from p.
      //@ assert p != 0; // Loop condition guarantees p is not null here.
      //@ tree_shape sl, sr;
      if(p->c) { 
        // Ascend from right child: restore p->r and move up.
        // The whole subtree at p is now marked.
        //@ assert p->m |-> true &*& p->c |-> true &*& s == ts_node(sl, sr);
        //@ assert p->l |-> ?pl &*& tree(pl, sl, true) &*& p->r |-> t &*& path(t, p, sr);
        struct node* q = t;
        t = p;
        p = p->r;
        t->r = q;
        //@ close tree(t, s, true);
        //@ close path(p, t, sr);
      } else { 
        // Ascend from left child: swing pointers to descend into right child.
        //@ assert p->m |-> true &*& p->c |-> false &*& s == ts_node(sl, sr);
        //@ assert p->r |-> ?pr &*& tree(pr, sr, false) &*& p->l |-> t &*& path(t, p, sl);
        struct node* q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close path(p, t, s);
      }
    } else { 
      // Descend: t is an unmarked node. Mark it and go left.
      //@ open tree(t, s, false);
      //@ tree_shape sl, sr;
      //@ assert s == ts_node(sl, sr);
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close path(p, t, s);
    }
  }
  //@ open path(p, t, s);
}

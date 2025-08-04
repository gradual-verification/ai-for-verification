#include "stdlib.h"

struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
  
};

/*@
// An untouched part of the tree. All nodes are unmarked.
predicate tree(struct node* n) =
  n == 0 ?
    true
  :
    n->m |-> false &*& n->c |-> false &*& n->l |-> ?l &*& n->r |-> ?r &*&
    malloc_block_node(n) &*&
    tree(l) &*& tree(r);

// A fully explored and marked part of thetree.
predicate marked_tree(struct node* n) =
  n == 0 ?
    true
  :
    n->m |-> true &*& n->c |-> _ &*& n->l |-> ?l &*& n->r |-> ?r &*&
    malloc_block_node(n) &*&
    marked_tree(l) &*& marked_tree(r);

// This predicate describes the state of the graph during the algorithm.
// It is defined recursively on the path from the root to 'p'.
// 'p' is the "parent" pointer in the algorithm, and 't' is the "current" pointer.
predicate sw_state(struct node* p, struct node* t) =
    p == 0 ?
        (t == 0 || t->m |-> false) &*& tree(t)
    :
        p->m |-> true &*&
        p->c |-> ?c &*&
        malloc_block_node(p) &*&
        (
            c ? // Ascending from right child. 'p's original right child was 't'.
                p->r |-> ?up &*&
                p->l |-> ?l &*&
                marked_tree(l) &*&
                sw_state(up, p)
            :   // Ascending from left child. 'p's original left child was 't'.
                p->l |-> ?up &*&
                p->r |-> ?r &*&
                tree(r) &*&
                sw_state(up, p)
        ) &*&
        (t == 0 || (t->m |-> true &*& marked_tree(t)));

@*/


// TODO: make this function pass the verification
/*
  **Function `schorr_waite`:**
  - **Description:** The `schorr_waite` function marks all nodes in a binary tree using the Schorr-Waite marking algorithm. 
  It operates without using additional memory for a stack, instead using the `m` and `c` fields of the nodes to manage the traversal.

  It requires that root is the root of a tree with all nodes unmarked, 
  and ensures that there exists a tree with all nodes marked after the function call.
*/
void schorr_waite(struct node* root)
    //@ requires tree(root);
    //@ ensures marked_tree(root);
{
  struct node* t = root; 
  struct node* p = 0;
 
  //@ close sw_state(0, root);
  while(p != 0 || (t != 0 && ! (t->m)))
    //@ invariant sw_state(p, t);
  {
    //@ open sw_state(p, t);
    if(t == 0 || t->m) {
      //@ assert p != 0;
      //@ open sw_state(p, t);
      if(p->c) { // Ascend from right child
        struct node* q = t;
        t = p;
        //@ open sw_state(p->r, p);
        p = p->r;
        t->r = q;
        //@ close marked_tree(t);
        //@ close sw_state(p, t);
      } else { // Ascend from left child, swing to right
        struct node* q = t;
        //@ open sw_state(p->l, p);
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close sw_state(p, t);
      }
    } else { // Descend
      struct node* q = p;
      p = t;
      //@ open tree(t);
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close sw_state(p, t);
    }
  }
  //@ open sw_state(p, t);
}

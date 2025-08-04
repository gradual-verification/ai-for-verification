#include <stdbool.h>

struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
};

/*@
predicate tree(struct node* t) = 
  t == 0 ? true : t->m |-> _ &*& t->c |-> _ &*& t->l |-> ?l &*& t->r |-> ?r &*& tree(l) &*& tree(r);

// Ghost predicate to anchor the path at the original root.
predicate is_root(struct node* r);

// A path from p back to the original root.
// The pointers are reversed.
// 't_child' is the node that was originally a child of 'p'.
predicate path(struct node* p, struct node* t_child) =
  p == 0 ?
    is_root(t_child)
  :
    p->m |-> true &*& p->c |-> ?c &*&
    (
      c == false ? // came from left child
        p->l |-> ?gp &*& p->r |-> ?r &*& tree(r) &*&
        path(gp, p)
      : // came from right child
        p->r |-> ?gp &*& p->l |-> ?l &*& tree(l) &*&
        path(gp, p)
    );

@*/


// TODO: make this function pass the verification
void schorr_waite(struct node* root) 
  //@ requires tree(root);
  //@ ensures tree(root);
{
  struct node* t = root; 
  struct node* p = 0;
  
  //@ produce_predicate is_root(root);
  //@ close path(0, root);

  while(p != 0 || (t != 0 && !t->m))
    //@ invariant path(p, t) &*& tree(t);
  {
    if(t == 0 || t->m) {
      // Ascend
      //@ open path(p, t);
      // Loop condition implies p != 0.
      // if (p == 0) { (t != 0 && !t->m) } which contradicts (t == 0 || t->m).
      // So p != 0.
      if(p->c) { 
        // Ascend from right child
        //@ assert p->r |-> ?gp &*& p->l |-> ?l &*& tree(l) &*& path(gp, p);
        struct node* q = t;
        t = p;
        p = p->r; // p becomes gp
        t->r = q; // t is old p, so old_p->r = t (old t)
        //@ close tree(t); // tree(old_p) is now restored
      } else { 
        // Ascend from left child, then descend to right child
        //@ assert p->l |-> ?gp &*& p->r |-> ?r &*& tree(r) &*& path(gp, p);
        struct node* q = t;
        t = p->r; // t becomes r
        p->r = p->l; // p->r becomes gp
        p->l = q; // p->l becomes old t
        p->c = true;
        //@ close path(p, t); // path(p, r) is now formed
      }
    } else {
      // Descend
      //@ open tree(t);
      //@ assert t->m |-> false &*& t->c |-> _ &*& t->l |-> ?l &*& t->r |-> ?r &*& tree(l) &*& tree(r);
      struct node* q = p;
      p = t;
      t = t->l; // t becomes l
      p->l = q; // p is old t, so old_t->l = old_p
      p->m = true;
      p->c = false;
      //@ close path(p, t); // path(old_t, l) is now formed
    }
  }
  
  //@ open path(p, t);
  //@ consume_predicate is_root(t);
  // From loop termination, p == 0.
  // open path(0, t) gives is_root(t).
  // consume is_root(t) proves t == root.
  // We are left with tree(t), which is tree(root).
}
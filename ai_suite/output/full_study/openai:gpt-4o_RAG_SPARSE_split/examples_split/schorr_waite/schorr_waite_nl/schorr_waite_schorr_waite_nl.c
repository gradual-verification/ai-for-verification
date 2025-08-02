#include "stdlib.h"

struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
};

//@ predicate tree(struct node* n; list<struct node*> nodes) = n == 0 ? nodes == nil : n->m |-> false &*& n->c |-> false &*& n->l |-> ?l &*& n->r |-> ?r &*& malloc_block_node(n) &*& tree(l, ?lnodes) &*& tree(r, ?rnodes) &*& nodes == cons(n, append(lnodes, rnodes));

//@ predicate marked_tree(struct node* n; list<struct node*> nodes) = n == 0 ? nodes == nil : n->m |-> true &*& n->c |-> _ &*& n->l |-> ?l &*& n->r |-> ?r &*& malloc_block_node(n) &*& marked_tree(l, ?lnodes) &*& marked_tree(r, ?rnodes) &*& nodes == cons(n, append(lnodes, rnodes));

//@ lemma void tree_marked_tree(struct node* n)
//@ requires tree(n, ?nodes);
//@ ensures marked_tree(n, nodes);
//@ {
//@   open tree(n, nodes);
//@   if (n != 0) {
//@     tree_marked_tree(n->l);
//@     tree_marked_tree(n->r);
//@     close marked_tree(n, nodes);
//@   }
//@ }

//@ lemma void marked_tree_tree(struct node* n)
//@ requires marked_tree(n, ?nodes);
//@ ensures tree(n, nodes);
//@ {
//@   open marked_tree(n, nodes);
//@   if (n != 0) {
//@     marked_tree_tree(n->l);
//@     marked_tree_tree(n->r);
//@     close tree(n, nodes);
//@   }
//@ }

//@ lemma void tree_distinct(struct node* n)
//@ requires tree(n, ?nodes);
//@ ensures tree(n, nodes) &*& distinct(nodes) == true;
//@ {
//@   open tree(n, nodes);
//@   if (n != 0) {
//@     tree_distinct(n->l);
//@     tree_distinct(n->r);
//@     distinct_append(append(?lnodes, ?rnodes), cons(n, nil));
//@     close tree(n, nodes);
//@   }
//@ }

//@ lemma void marked_tree_distinct(struct node* n)
//@ requires marked_tree(n, ?nodes);
//@ ensures marked_tree(n, nodes) &*& distinct(nodes) == true;
//@ {
//@   open marked_tree(n, nodes);
//@   if (n != 0) {
//@     marked_tree_distinct(n->l);
//@     marked_tree_distinct(n->r);
//@     distinct_append(append(?lnodes, ?rnodes), cons(n, nil));
//@     close marked_tree(n, nodes);
//@   }
//@ }

//@ lemma void tree_subset(struct node* n, list<struct node*> nodes)
//@ requires tree(n, ?allNodes) &*& subset(nodes, allNodes) == true;
//@ ensures tree(n, allNodes) &*& subset(nodes, allNodes) == true;
//@ {
//@   open tree(n, allNodes);
//@   if (n != 0) {
//@     tree_subset(n->l, nodes);
//@     tree_subset(n->r, nodes);
//@     close tree(n, allNodes);
//@   }
//@ }

//@ lemma void marked_tree_subset(struct node* n, list<struct node*> nodes)
//@ requires marked_tree(n, ?allNodes) &*& subset(nodes, allNodes) == true;
//@ ensures marked_tree(n, allNodes) &*& subset(nodes, allNodes) == true;
//@ {
//@   open marked_tree(n, allNodes);
//@   if (n != 0) {
//@     marked_tree_subset(n->l, nodes);
//@     marked_tree_subset(n->r, nodes);
//@     close marked_tree(n, allNodes);
//@   }
//@ }

/*@
predicate_family_instance thread_run_pre(schorr_waite)(struct node* root, list<struct node*> nodes) =
  tree(root, nodes) &*& distinct(nodes) == true;

predicate_family_instance thread_run_post(schorr_waite)(struct node* root, list<struct node*> nodes) =
  marked_tree(root, nodes) &*& distinct(nodes) == true;
@*/

// TODO: make this function pass the verification
void schorr_waite(struct node* root) 
  //@ requires thread_run_pre(schorr_waite)(root, ?nodes);
  //@ ensures thread_run_post(schorr_waite)(root, nodes);
{
  struct node* t = root; 
  struct node* p = 0;
 
  while(p != 0 || (t != 0 && ! (t->m)))
  //@ invariant tree(t, ?tnodes) &*& tree(p, ?pnodes) &*& subset(tnodes, nodes) == true &*& subset(pnodes, nodes) == true &*& distinct(nodes) == true;
  {
    if(t == 0 || t->m) {
      if(p->c) { 
        struct node* q = t;
        t = p;
        p = p->r;
        t->r = q;
      } else { 
        struct node* q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
      }
    } else { 
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
    }
  }
  //@ tree_marked_tree(root);
}
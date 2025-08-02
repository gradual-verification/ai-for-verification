#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

struct node {
  bool m;
  bool c; 
  struct node* l;
  struct node* r;
};

/*@
predicate tree(struct node* t, bool marked) = 
  t==0 ? true : t->m |-> marked &*& t->c |-> ?c &*& t->l |-> ?l &*& t->r |-> ?r &*& tree(l, marked) &*& tree(r, marked);
@*/

// TODO: make this function pass the verification
void schorr_waite(struct node* root) 
  //@ requires tree(root, false);
  //@ ensures tree(_, true);
{
  struct node* t = root; 
  struct node* p = 0;
 
  while(p != 0 || (t != 0 && ! (t->m)))
  //@ invariant tree(t, false) &*& tree(p, true);
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
  //@ close tree(t, true);
  //@ close tree(p, true);
}
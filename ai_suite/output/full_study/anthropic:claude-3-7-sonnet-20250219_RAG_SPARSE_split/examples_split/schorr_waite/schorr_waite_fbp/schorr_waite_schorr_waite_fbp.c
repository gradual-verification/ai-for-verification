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
 
  //@ open tree(root, false);
  //@ if (root == 0) { close tree(0, true); return; }
  //@ close tree(root, false);
  
  while(p != 0 || (t != 0 && ! (t->m)))
    /*@
    invariant 
      p == 0 ? 
        (t == 0 ? tree(0, true) : tree(t, false)) 
      : 
        p->m |-> true &*& p->c |-> ?pc &*& 
        (pc ? 
          p->l |-> ?pl &*& p->r |-> t &*& tree(pl, true) 
        : 
          p->l |-> t &*& p->r |-> ?pr &*& tree(pr, true)) &*& 
        (t == 0 ? true : t->m |-> ?tm &*& t->c |-> ?tc &*& t->l |-> ?tl &*& t->r |-> ?tr &*& 
          (tm ? tree(tl, true) &*& tree(tr, true) : tree(tl, false) &*& tree(tr, false)));
    @*/
  {
    if(t == 0 || t->m) {
      if(p->c) { 
        struct node* q = t;
        t = p;
        p = p->r;
        t->r = q;
        //@ if (q == 0) { open tree(q, true); }
      } else { 
        struct node* q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ if (q == 0) { open tree(q, true); }
      }
    } else { 
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ if (t == 0) { open tree(t, false); close tree(t, true); }
    }
  }
  
  //@ open tree(0, true);
  //@ close tree(0, true);
}
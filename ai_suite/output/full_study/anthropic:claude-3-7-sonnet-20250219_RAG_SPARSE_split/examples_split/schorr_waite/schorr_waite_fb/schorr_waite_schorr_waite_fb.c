struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
};

/*@
predicate tree(struct node* t) = 
  t == 0 ? true : t->m |-> _ &*& t->c |-> _ &*& t->l |-> ?l &*& t->r |-> ?r &*& tree(l) &*& tree(r);
@*/

// TODO: make this function pass the verification
void schorr_waite(struct node* root) 
  //@ requires tree(root);
  //@ ensures tree(_);
{
  struct node* t = root; 
  struct node* p = 0;

  /*@
  // Define a predicate for the marking stack
  predicate mark_stack(struct node* p, struct node* t) =
    p == 0 ?
      true
    :
      p->m |-> true &*& p->c |-> ?c &*& 
      (c ? 
        p->l |-> ?l &*& p->r |-> t &*& mark_stack(l, p)
      : 
        p->l |-> t &*& p->r |-> ?r &*& mark_stack(r, p));
  @*/

  //@ close mark_stack(p, t);
  
  while(p != 0 || (t != 0 && !t->m))
    /*@
    invariant 
      mark_stack(p, t) &*&
      (t == 0 ? true : t->m |-> ?tm &*& t->c |-> ?tc &*& t->l |-> ?tl &*& t->r |-> ?tr &*&
        (tm ? tree(tl) &*& tree(tr) : true));
    @*/
  {
    if(t == 0 || t->m) {
      //@ open mark_stack(p, t);
      if(p->c) { 
        struct node* q = t;
        t = p;
        p = p->r;
        t->r = q;
        //@ close mark_stack(p, t);
      } else { 
        struct node* q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        //@ close mark_stack(p, t);
      }
    } else {
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ close mark_stack(p, t);
    }
  }
  
  //@ open mark_stack(p, t);
  //@ close tree(root);
}
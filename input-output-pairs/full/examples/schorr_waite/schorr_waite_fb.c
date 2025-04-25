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
void schorr_waite(struct node* root) 
  //@ requires tree(root);
  //@ ensures tree(_);
{
  struct node* t = root; 
  struct node* p = 0;

  while(p != 0 || (t != 0 && !t->m))
    
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
    } else { // push
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
     
    }
  }
 
}

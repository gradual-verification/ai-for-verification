struct node {
  bool m;
  bool c; 
  struct node* l;
  struct node* r;
  
};

/*@
predicate tree(struct node* t, bool marked) = 
  t==0 ? true : t->m |-> marked &*& t->c |-> ?c &*& t->l |-> ?l &*& t->r |-> ?r &*& tree(l, marked) &*& tree(r, marked);
  
predicate stack(struct node* t) =
  t == 0 ? true : t->m |-> true &*& t->c |-> ?c &*& t->l |-> ?l &*& t->r |-> ?r &*& (c == false ? stack(l) &*& tree(r, false) : stack(r) &*& tree(l, true));

@*/

void schorr_waite(struct node* root) 
  //@ requires tree(root, false);
  //@ ensures tree(_, true);
{
  struct node* t = root; 
  struct node* p = 0;
 
  while(p != 0 || (t != 0 && ! (t->m)))
   
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

}
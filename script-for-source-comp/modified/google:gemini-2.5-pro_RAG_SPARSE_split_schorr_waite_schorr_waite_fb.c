
struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
};



void schorr_waite(struct node* root) 
{
  struct node* t = root; 
  struct node* p = 0;
  

  while(p != 0 || (t != 0 && !t->m))
  {
    if(t == 0 || t->m) {
      if(p->c) { 
        struct node* q = t;
        t = p;
        p = p->r; // p becomes gp
        t->r = q; // t is old p, so old_p->r = t (old t)
      } else { 
        struct node* q = t;
        t = p->r; // t becomes r
        p->r = p->l; // p->r becomes gp
        p->l = q; // p->l becomes old t
        p->c = true;
      }
    } else {
      struct node* q = p;
      p = t;
      t = t->l; // t becomes l
      p->l = q; // p is old t, so old_t->l = old_p
      p->m = true;
      p->c = false;
    }
  }
  
}

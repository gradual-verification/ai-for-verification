
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
 
  while(p != 0 || (t != 0 && ! (t->m)))
  {
    if(t == 0 || t->m) {
      if(p->c) { // Ascend from right child
        struct node* q = t;
        t = p;
        p = p->r;
        t->r = q;
      } else { // Ascend from left child, swing to right
        struct node* q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
      }
    } else { // Descend
      struct node* q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
    }
  }
}

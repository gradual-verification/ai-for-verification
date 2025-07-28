#include "stdlib.h"

struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
  
};




// TODO: make this function pass the verification
/*
  **Function `schorr_waite`:**
  - **Description:** The `schorr_waite` function marks all nodes in a binary tree using the Schorr-Waite marking algorithm. 
  It operates without using additional memory for a stack, instead using the `m` and `c` fields of the nodes to manage the traversal.

  It requires that root is the root of a tree with all nodes unmarked, 
  and ensures that there exists a tree with all nodes marked after the function call.
*/
void schorr_waite(struct node* root) 
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

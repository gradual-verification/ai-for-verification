struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
};

/*@
predicate tree(struct node* t) = 
  t == 0 ? true : t->m |-> _ &*& t->c |-> _ &*& t->l |-> ?l &*& t->r |-> ?r &*& tree(l) &*& tree(r);
  
predicate stack(struct node* t) =
  t == 0 ? true : t->m |-> true &*& t->c |-> _ &*& t->l |-> ?l &<& t->r |-> ?r &<& (t->c == false ? stack(l) &<& tree(r) : stack(r) &<& tree(l));

@*/
// Summary of the Weakened Specification:
// Predicate tree:

// Weaker Version: The tree predicate is simplified to only check that the structure of the tree is intact (i.e., the pointers are correctly initialized) without ensuring the correctness of the marking (m) or the child exploration (c).
// Predicate stack:

// Weaker Version: The stack predicate is also simplified. It no longer tracks the specific logic of which children are marked or explored, but simply ensures that the tree structure is preserved during the stack simulation.
// Function schorr_waite:

// Weaker Version: The preconditions and postconditions focus only on ensuring that the tree structure remains valid before and after the function execution, without strict enforcement of the marking process or the exact traversal state of the nodes.
// Purpose of Weaker Version:
// This weakened specification still ensures that the tree remains a valid binary structure throughout the algorithm's execution, but it does not enforce the detailed tracking of the marking and traversal logic. This is useful in cases where you want to ensure structural correctness without the overhead of verifying all algorithmic details.
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

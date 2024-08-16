#include "stdlib.h"

struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
  
};



/*
  **Function `schorr_waite`:**
  - **Description:** The `schorr_waite` function marks all nodes in a binary tree using the Schorr-Waite marking algorithm. It operates without using additional memory for a stack, instead using the `m` and `c` fields of the nodes to manage the traversal.
  - **Parameters:**
    - `root` (struct node*): Pointer to the root of the binary tree.
  - **Precondition:** The function requires that the tree rooted at `root` is initially unmarked (`tree(root, false)`).
  - **Postcondition:** After the function completes, all nodes in the tree are marked (`tree(_, true)`).
  - **Detailed Operation:**
    - The function uses two pointers, `t` and `p`, to traverse the tree.
      - `t` tracks the current node being processed.
      - `p` simulates the stack, representing the path back to the root.
    - The algorithm alternates between three operations:
      1. **Push:** If the current node `t` is unmarked, it is marked, and traversal continues to its left child.
      2. **Swing:** If the current node `t` is marked but not fully explored, the algorithm swings to its right child, reversing the left child link temporarily.
      3. **Pop:** If the current node `t` is fully explored (both children have been traversed), the algorithm pops back to the previous node in the simulated stack, restoring the tree structure.
    - The loop continues until the entire tree has been traversed and marked.
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

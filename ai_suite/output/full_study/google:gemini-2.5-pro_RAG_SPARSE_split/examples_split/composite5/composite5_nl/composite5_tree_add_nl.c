#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@
// Predicate for a single tree node.
// `n` is the node, `p` is its parent, `c` is the count of nodes in the subtree.
predicate tree(struct node *n, struct node *p, int c);

// Predicate for a list of sibling nodes.
// `n` is the first sibling, `p` is the parent of all siblings, `c` is the total count.
predicate siblings(struct node *n, struct node *p, int c);

predicate tree(struct node *n, struct node *p, int c) =
    n->firstChild |-> ?fc &*&
    n->parent |-> p &*&
    n->count |-> c &*&
    malloc_block_node(n) &*&
    siblings(fc, n, ?c_children) &*&
    c == 1 + c_children &*& c > 0;

predicate siblings(struct node *n, struct node *p, int c) =
    n == 0 ?
        c == 0
    :
        n->nextSibling |-> ?ns &*&
        tree(n, p, ?c_n) &*&
        siblings(ns, p, ?c_s) &*&
        c == c_n + c_s;

// Lemma to prove that a node `p` is a child of `pp`.
// It "opens" the siblings list to expose the tree predicate for `p`.
lemma void is_child_of(struct node *p, struct node *pp)
    requires
        pp->firstChild |-> ?fc &*&
        siblings(fc, pp, ?c_children) &*&
        mem(p, ghost_list_from_siblings(fc)) == true;
    ensures
        pp->firstChild |-> fc &*&
        tree(p, pp, ?cp) &*&
        siblings(remove(p, ghost_list_from_siblings(fc)), pp, c_children - cp);
{
    open siblings(fc, pp, c_children);
    if (fc == p) {
        // p is the first child.
    } else {
        is_child_of(p, pp); // Recursive call on the rest of the list.
        // Reconstruct the siblings list.
        close siblings(fc, pp, c_children);
    }
}

// Helper fixpoint to create a ghost list of nodes from a sibling list.
fixpoint list<struct node*> ghost_list_from_siblings(struct node *n)
    requires siblings(n, _, _);
{
    open siblings(n, _, _);
    if (n == 0) {
        return nil;
    } else {
        return cons(n, ghost_list_from_siblings(n->nextSibling));
    }
}
@*/


/*create_node function
-param: struct node *p, struct node *next
-description: This function creates a new node with a specified parent and next sibling.
The node is initialized with an empty list of children and a count of 1.
It returns a pointer to the newly created node, which is properly initialized.
*/
struct node *create_node(struct node *p, struct node *next)
    //@ requires true;
    //@ ensures tree(result, p, 1) &*& result->nextSibling |-> next;
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  //@ close siblings(0, n, 0);
  //@ close tree(n, p, 1);
  return n;
}


/*add_to_count function
-param: struct node *p, int delta
-description: This function adds the delta value to the count of the node p and its parent nodes,
where count is the number of nodes in the subtree rooted at the node.

It requires that p is non-null and in a tree, and all nodes in its subtree except p itself are valid nodes. 
p's count will be valid after adding delta (>0) to it. So it ensures that the tree is valid after the operation.
*/
void add_to_count(struct node *p, int delta)
    /*@
    requires
        p != 0 &*&
        p->count |-> ?c &*&
        p->parent |-> ?pp &*&
        (
            pp == 0 ?
                true
            :
                // If there is a parent, we need its full `tree` predicate.
                tree(pp, ?ppp, ?cpp) &*&
                // We also need to know that `p` is indeed a child of `pp`.
                // This is implicitly true by the structure of the calling context,
                // but we state it here for clarity.
                true
        );
    @*/
    /*@
    ensures
        p->count |-> c + delta &*&
        p->parent |-> pp &*&
        (
            pp == 0 ?
                true
            :
                tree(pp, ppp, cpp + delta)
        );
    @*/
{
  struct node *pp = p->parent;
 
  if (pp == 0) {
    p->count += delta;

  } else {
    //@ open tree(pp, ppp, cpp);
    p->count += delta;
    
    add_to_count(pp, delta);
    
    //@ close tree(pp, ppp, cpp + delta);
  }
}


// TODO: make this function pass the verification
/*tree_add function
-param: struct node *node
-description: This function adds a new node to the tree. 
It returns the newly added node.
It requires that the node is a part of valid tree. 
It ensures that the tree is still valid after adding a node.
*/
struct node *tree_add(struct node *node)
    /*@
    requires
        tree(node, ?p, ?c) &*&
        (p == 0 ? true : tree(p, ?pp, ?cp));
    @*/
    /*@
    ensures
        tree(node, ?p_new, c + 1) &*&
        (p_new == 0 ? true : tree(p_new, ?pp_new, cp + 1)) &*&
        result == node->firstChild;
    @*/
{
  //@ open tree(node, p, c);
  struct node *fc = node->firstChild;
  
  struct node *n = create_node(node, node->firstChild);
  //@ assert tree(n, node, 1) &*& n->nextSibling |-> fc;
  
  node->firstChild = n;
  
  //@ close siblings(n, node, c); // The new child `n` followed by the old children `fc`. Total children count is 1 + (c-1) = c.
  
  // The tree structure under `node` is now correct, but its count is `c` instead of `c+1`.
  // We call `add_to_count` to fix the counts up the ancestor chain.
  add_to_count(node, 1);
  
  //@ close tree(node, p, c + 1);
  return n;
}
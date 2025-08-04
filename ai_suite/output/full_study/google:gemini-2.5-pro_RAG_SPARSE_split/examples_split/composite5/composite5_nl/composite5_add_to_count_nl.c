#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@

// A predicate for the parts of a node's data that are not touched by add_to_count.
// It owns the 'firstChild' and 'nextSibling' fields.
predicate node_children_and_siblings_p(struct node *n) =
    n->firstChild |-> _ &*&
    n->nextSibling |-> _;

// A predicate representing the parent pointers and counts for a path to the root.
// It owns the node itself, and its 'parent' and 'count' fields, for each node on the path.
predicate path(struct node *p; list<int> counts) =
    p == 0 ?
        counts == nil
    :
        p != 0 &*&
        malloc_block_node(p) &*&
        node_children_and_siblings_p(p) &*&
        p->parent |-> ?pp &*&
        p->count |-> ?c &*&
        path(pp, ?counts_tail) &*&
        counts == cons(c, counts_tail);

// A fixpoint function to add a value to an integer. Used for mapping over the list of counts.
fixpoint int add(int d, int x) { return x + d; }

@*/

// TODO: make this function pass the verification
/*add_to_count function
-param: struct node *p, int delta
-description: This function adds the delta value to the count of the node p and its parent nodes,
where count is the number of nodes in the subtree rooted at the node.

It requires that p is non-null and in a tree, and all nodes in its subtree except p itself are valid nodes. 
p's count will be valid after adding delta (>0) to it. So it ensures that the tree is valid after the operation.
*/
void add_to_count(struct node *p, int delta)
    //@ requires p != 0 &*& path(p, ?counts);
    //@ ensures path(p, map((add)(delta), counts));
{
  //@ open path(p, counts);
  struct node *pp = p->parent;
 
  if (pp == 0) {
    p->count += delta;
    //@ close path(0, nil);
  } else {
    p->count += delta;
    add_to_count(pp, delta);
    //@ assert path(pp, map(add(delta), tail(counts)));
  }
  //@ close path(p, map(add(delta), counts));
}
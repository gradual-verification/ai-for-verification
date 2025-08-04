#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@
// A forest is a list of sibling trees.
// 'n' is the head of the list of siblings.
// 'p' is the parent of all trees in the forest.
// 'c' is the total number of nodes in the forest.
predicate forest(struct node *n, struct node *p, int c);

// A tree is a node and a forest of its children.
// 'n' is the root of the tree.
// 'p' is the parent of the root node 'n'.
// 'c' is the total number of nodes in the tree.
predicate tree(struct node *n, struct node *p, int c) =
    n->firstChild |-> ?fc &*&
    n->parent |-> p &*&
    n->count |-> c &*&
    malloc_block_node(n) &*&
    forest(fc, n, ?child_count) &*&
    c == 1 + child_count;

predicate forest(struct node *n, struct node *p, int c) =
    n == 0 ?
        c == 0
    :
        n->nextSibling |-> ?ns &*&
        tree(n, p, ?c1) &*&
        forest(ns, p, ?c2) &*&
        c == c1 + c2;
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
  //@ close forest(0, n, 0);
  //@ close tree(n, p, 1);
  return n;
}


// TODO: make this function pass the verification
/*create_tree function
-param: none
-description: This function creates a new tree.
It returns a pointer to the root node of the newly created tree. 
The tree is properly initialized with the root node as the only node.
*/
struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, 0, 1) &*& result->nextSibling |-> 0;
{
  struct node *n = create_node(0, 0);
  return n;
}
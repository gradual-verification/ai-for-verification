#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>
//@ #include "ghostlist.gh"

// Some general infrastructure; should be in the VeriFast Library.

/*
  Natural Language Specification:
  - Description: The code implements a tree structure where each node can have multiple children and a parent, and maintains a ghost list of children for verification purposes. The code includes functions to create nodes, add nodes to the tree, and retrieve the parent of a node.
  - Terminology:
    - **Ghost List**: A conceptual list used for verification purposes in the VeriFast framework, representing a list of nodes (children) associated with a particular parent node.
    - **Predicate**: Conditions used to describe the structure and relationships of nodes within the tree, ensuring correctness during verification.
*/

/*@
predicate foreach2<a, b>(list<a> as, list<b> bs, predicate(a, b) p) =
  switch (as) {
    case nil: return bs == nil;
    case cons(a, as0): return
      switch (bs) {
        case nil: return false;
        case cons(b, bs0): return
          p(a, b) &*& foreach2(as0, bs0, p);
      };
  };

fixpoint list<b> remove_assoc<a, b>(a a, list<a> as, list<b> bs);
fixpoint b assoc2<a, b>(a a, list<a> as, list<b> bs);

lemma void foreach2_remove<a, b>(list<a> as, a a);
  requires foreach2<a, b>(as, ?bs, ?p) &*& mem(a, as) == true;
  ensures foreach2<a, b>(remove(a, as), remove_assoc(a, as, bs), p) &*& p(a, assoc2(a, as, bs)) &*& length(bs) == length(as);

fixpoint list<b> update2<a, b>(a a, b b, list<a> as, list<b> bs);

lemma void foreach2_unremove<a, b>(list<a> as, list<b> bs, a a, b b);
  requires foreach2<a, b>(remove(a, as), remove_assoc(a, as, bs), ?p) &*& mem(a, as) == true &*& p(a, b) &*& length(bs) == length(as);
  ensures foreach2<a, b>(as, update2(a, b, as, bs), p);

fixpoint int sum(list<int> xs) {
  switch (xs) {
    case nil: return 0;
    case cons(x, xs0): return x + sum(xs0);
  }
}

lemma void sum_update2<a>(a a, int b, list<a> as, list<int> bs);
  requires length(bs) == length(as);
  ensures sum(update2(a, b, as, bs)) == sum(bs) + b - assoc2(a, as, bs);

lemma void neq_mem_remove<t>(t x1, t x2, list<t> xs)
  requires x1 != x2 &*& mem(x1, xs) == true;
  ensures mem(x1, remove(x2, xs)) == true;
{
  switch (xs) {
    case nil:
    case cons(x, xs0):
      if (x == x1 || x == x2) {
      } else {
        neq_mem_remove(x1, x2, xs0);
      }
  }
}

lemma void remove_commut<t>(t x1, t x2, list<t> xs);
  requires true;
  ensures remove(x1, remove(x2, xs)) == remove(x2, remove(x1, xs));

@*/
/*
  Natural Language Specification:
  - Description: A node structure representing a single node in a tree. Each node can have a parent, siblings, and multiple children. The `count` field keeps track of the number of nodes in the subtree rooted at this node.
  - Fields:
    - `firstChild`: Pointer to the first child node.
    - `nextSibling`: Pointer to the next sibling node.
    - `parent`: Pointer to the parent node.
    - `count`: Integer representing the number of nodes in the subtree rooted at this node.
*/
struct node {
  //@ int childrenGhostListId;
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};





/*
  Natural Language Specification:
  - Description: Creates a new node with a specified parent and next sibling. The node is initialized with an empty list of children and a count of 1.
  - Parameters:
    - `p`: A pointer to the parent node.
    - `next`: A pointer to the next sibling node.
  - Requires: No specific preconditions.
  - Ensures: Returns a pointer to the newly created node, which is properly initialized.
*/
struct node *create_node(struct node *p, struct node *next)
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();

  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;

  return n;
}

/*
  Natural Language Specification:
  - Description: Creates a new tree with a single root node.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: Returns a pointer to the root node of the newly created tree. The tree is properly initialized with the root node as the only node.
*/
struct node *create_tree()
{
  struct node *n = create_node(0, 0);
  return n;
}

/*
  Natural Language Specification:
  - Description: Increments the count of nodes in the subtree rooted at a given node and all of its ancestors by a specified amount.
  - Parameters:
    - `p`: A pointer to the node whose count is to be incremented.
    - `delta`: The amount by which to increment the count.
  - Requires: The node `p` is part of a valid tree.
  - Ensures: The counts of all affected nodes are correctly updated.
*/
void add_to_count(struct node *p, int delta)
{
  struct node *pp = p->parent;
  if (pp == 0) {
    p->count += delta;
  } else {
    p->count += delta;
    add_to_count(pp, delta);
  }
}

/*
  Natural Language Specification:
  - Description: Adds a new child node to a given node in the tree.
  - Parameters:
    - `node`: A pointer to the parent node to which the new child will be added.
  - Requires: The node is part of a valid tree.
  - Ensures: The tree is updated to include the new child node, and the parent's child count is incremented.
*/
struct node *tree_add(struct node *node)
{
  struct node *n = create_node(node, node->firstChild);
  node->firstChild = n;
  add_to_count(node, 1);
  return n;
}

/*
  Natural Language Specification:
  - Description: Retrieves the parent node of a given node in the tree.
  - Parameters:
    - `node`: A pointer to the node whose parent is to be retrieved.
  - Requires: The node is part of a valid tree.
  - Ensures: Returns a pointer to the parent node, or `0` if the node is the root.
*/
struct node *tree_get_parent(struct node *node)
{
  struct node *p = node->parent;
  return p;
}

/*
  Natural Language Specification:
  - Description: Main function to demonstrate the creation and manipulation of a tree structure. The function creates a tree, adds nodes, retrieves parent nodes, and performs various operations on the tree.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: The tree operations are demonstrated, and the program terminates successfully.
*/
int main0()
{
  struct node *node = create_tree();
  node = tree_add(node);
  node = tree_add(node);
  node = tree_get_parent(node);
  if (node == 0) abort();
  node = tree_add(node);
  node = tree_get_parent(node);
  if (node == 0) abort();
  node = tree_get_parent(node);
  if (node == 0) abort();
  //@ leak tree(_);
  return 0;
}

/*
  Natural Language Specification:
  - Description: Another main function to demonstrate the creation and manipulation of a tree structure with a more complex sequence of operations, including adding and linking multiple nodes.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: The tree operations are demonstrated, and the program terminates successfully.
*/
int main() //@ : main
{
    struct node *root = create_tree();
    struct node *left = tree_add(root);
    struct node *leftRight = tree_add(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    struct node *leftLeft = tree_add(left);
    struct node *leftRightRight = tree_add(leftRight);
    return 0;
}

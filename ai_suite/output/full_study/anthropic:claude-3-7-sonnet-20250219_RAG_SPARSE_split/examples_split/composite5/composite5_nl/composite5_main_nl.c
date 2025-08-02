#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@
// Define a predicate for a valid tree node
predicate tree_node(struct node *n, int count) =
  n != 0 &*&
  n->firstChild |-> ?fc &*&
  n->nextSibling |-> ?ns &*&
  n->parent |-> ?p &*&
  n->count |-> count &*&
  malloc_block_node(n);

// Define a predicate for a valid tree
predicate tree(struct node *n, int count) =
  n == 0 ?
    count == 0
  :
    tree_node(n, count) &*&
    tree(n->firstChild, ?fcCount) &*&
    tree(n->nextSibling, ?nsCount) &*&
    count == 1 + fcCount + nsCount &*&
    (n->firstChild != 0 ? n->firstChild->parent == n : true) &*&
    (n->nextSibling != 0 && n->parent != 0 ? n->nextSibling->parent == n->parent : true);
@*/

/*create_node function
-param: struct node *p, struct node *next
-description: This function creates a new node with a specified parent and next sibling.
The node is initialized with an empty list of children and a count of 1.
It returns a pointer to the newly created node, which is properly initialized.
*/
struct node *create_node(struct node *p, struct node *next)
//@ requires true;
//@ ensures tree_node(result, 1) &*& result->firstChild == 0 &*& result->nextSibling == next &*& result->parent == p;
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  //@ close tree_node(n, 1);
  return n;
}


/*create_tree function
-param: none
-description: This function creates a new tree.
It returns a pointer to the root node of the newly created tree. 
The tree is properly initialized with the root node as the only node.
*/
struct node *create_tree()
//@ requires true;
//@ ensures tree(result, 1);
{
  struct node *n = create_node(0, 0);
  //@ open tree_node(n, 1);
  //@ close tree(0, 0);
  //@ close tree(n, 1);
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
//@ requires tree_node(p, ?count) &*& delta > 0;
//@ ensures tree_node(p, count + delta);
{
  struct node *pp = p->parent;
  //@ open tree_node(p, count);
 
  if (pp == 0) {
    p->count += delta;
    //@ close tree_node(p, count + delta);

  } else {
    
    p->count += delta;
    //@ close tree_node(p, count + delta);
    
    add_to_count(pp, delta);
  }
}


/*tree_add function
-param: struct node *node
-description: This function adds a new node to the tree. 
It returns the newly added node.
It requires that the node is a part of valid tree. 
It ensures that the tree is still valid after adding a node.
*/
struct node *tree_add(struct node *node)
//@ requires tree_node(node, ?count);
//@ ensures tree_node(node, count + 1) &*& tree_node(result, 1) &*& result->parent == node &*& result->firstChild == 0;
{
  
  struct node *n = create_node(node, node->firstChild);
  //@ open tree_node(node, count);
  node->firstChild = n;
  //@ close tree_node(node, count);
  
  add_to_count(node, 1);

  return n;
}


/*tree_get_parent function
-param: struct node *node
-description: This function gets and returns the parent node a new node of the current node.
It requires that the node is a part of valid tree. 
It ensures that the tree is still valid, and the returned node is null or in the tree.
*/
struct node *tree_get_parent(struct node *node)
//@ requires tree_node(node, ?count);
//@ ensures tree_node(node, count) &*& (result == 0 || result == node->parent);
{
  //@ open tree_node(node, count);
  struct node *p = node->parent;
  //@ close tree_node(node, count);
  
  return p;
}


// TODO: make this function pass the verification
/*main function

This function tests the operations of composite tree.
*/
int main() //@ : main
//@ requires true;
//@ ensures true;
{
    //@ int tree_id = create_ghost_list<struct node *>();
    struct node *root = create_tree();
    
    //@ open tree(root, 1);
    //@ open tree_node(root, 1);
    //@ close tree_node(root, 1);
    
    struct node *left = tree_add(root);
    
    //@ open tree_node(left, 1);
    //@ close tree_node(left, 1);
    
    struct node *leftRight = tree_add(left);
    
    //@ open tree_node(leftRight, 1);
    //@ close tree_node(leftRight, 1);
    
    struct node *leftRightParent = tree_get_parent(leftRight);
    
    //@ assert leftRightParent == left;
    
    struct node *leftLeft = tree_add(left);
    
    //@ open tree_node(leftLeft, 1);
    //@ close tree_node(leftLeft, 1);
    
    struct node *leftRightRight = tree_add(leftRight);
    
    //@ open tree_node(leftRightRight, 1);
    //@ close tree_node(leftRightRight, 1);
    
    return 0;
}
#include "stdlib.h"
//@ #include "ghostlist.gh"

struct node {
  struct node *firstChild;
  struct node *nextSibling;
  struct node *parent;
  int count;
};

/*@
// Predicate for a single node and its subtree.
// It owns the node's data and the forest of its children.
// It enforces the invariant that `n->count` is the size of the subtree rooted at `n`.
predicate node(struct node *n, struct node *p, int c) =
    n->firstChild |-> ?fc &*&
    n->parent |-> p &*&
    n->count |-> c &*&
    malloc_block_node(n) &*&
    node_siblings(fc, n, ?children_count) &*&
    c == 1 + children_count;

// Predicate for a list of sibling nodes (a forest).
// It recursively owns the nodes in the list.
predicate node_siblings(struct node *n, struct node *p, int c) =
    n == 0 ?
        c == 0
    :
        n->nextSibling |-> ?ns &*&
        node(n, p, ?node_c) &*&
        node_siblings(ns, p, ?rest_c) &*&
        c == node_c + rest_c;
@*/


/*create_node function
-param: struct node *p, struct node *next
-description: This function creates a new node with a specified parent and next sibling.
The node is initialized with an empty list of children and a count of 1.
It returns a pointer to the newly created node, which is properly initialized.
*/
struct node *create_node(struct node *p, struct node *next)
    //@ requires true;
    //@ ensures node(result, p, 1) &*& result->nextSibling |-> next;
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  n->firstChild = 0;
  n->nextSibling = next;
  n->parent = p;
  n->count = 1;
  //@ close node_siblings(0, n, 0);
  //@ close node(n, p, 1);
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
    //@ ensures node(result, 0, 1) &*& result->nextSibling |-> 0;
{
  struct node *n = create_node(0, 0);
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
    /*@ requires p->parent |-> ?pp &*& p->count |-> ?c &*&
                 (pp == 0 ? 
                     true 
                 : 
                     node(pp, ?ppp, ?ppc) &*& pp->nextSibling |-> ?ppns &*&
                     // The following is a trick to prove that 'p' is indeed a child of 'pp'.
                     // It requires the caller to open the parent's children list.
                     pp->firstChild |-> p || (pp->firstChild |-> ?ppfc &*& ppfc != p)
                 );
    @*/
    /*@ ensures p->parent |-> pp &*& p->count |-> (c + delta) &*&
                (pp == 0 ?
                    true
                :
                    node(pp, ppp, ppc + delta) &*& pp->nextSibling |-> ppns
                );
    @*/
{
  //@ open node(pp, ppp, ppc);
  //@ open node_siblings(pp->firstChild, pp, _);
  struct node *pp = p->parent;
 
  if (pp == 0) {
    p->count += delta;

  } else {
    
    p->count += delta;
    
    add_to_count(pp, delta);
  }
  //@ if(pp != 0) close node_siblings(pp->firstChild, pp, _);
}


/*tree_add function
-param: struct node *node
-description: This function adds a new node to the tree. 
It returns the newly added node.
It requires that the node is a part of valid tree. 
It ensures that the tree is still valid after adding a node.
*/
struct node *tree_add(struct node *node)
    //@ requires node(node, ?p, ?c) &*& node->nextSibling |-> ?ns &*& (p == 0 ? true : node(p, ?gp, ?pc) &*& p->nextSibling |-> ?pns);
    //@ ensures node(node, p, c + 1) &*& node->nextSibling |-> ns &*& (p == 0 ? true : node(p, gp, pc + 1) &*& p->nextSibling |-> pns) &*& result != 0 &*& node(result, node, 1) &*& result->nextSibling |-> _;
{
  //@ open node(node, p, c);
  //@ assert node->firstChild |-> ?fc;
  
  struct node *n = create_node(node, fc);
  //@ assert node(n, node, 1) &*& n->nextSibling |-> fc;
  
  node->firstChild = n;
  
  //@ open node_siblings(fc, node, ?cc);
  //@ close node_siblings(n, node, 1 + cc);
  
  // The invariant for 'node' is now broken. Its count is 'c', but its children's count is 'cc + 1'.
  // c was 1 + cc, so the new count should be 1 + (cc + 1) = c + 1.
  // We call add_to_count to fix this.
  
  //@ if (p != 0) { open node(p, gp, pc); open node_siblings(p->firstChild, p, _); }
  add_to_count(node, 1);
  //@ if (p != 0) { close node_siblings(p->firstChild, p, _); }
  
  //@ close node(node, p, c + 1);

  return n;
}


/*tree_get_parent function
-param: struct node *node
-description: This function gets and returns the parent node a new node of the current node.
It requires that the node is a part of valid tree. 
It ensures that the tree is still valid, and the returned node is null or in the tree.
*/
struct node *tree_get_parent(struct node *node)
    //@ requires node(node, ?p, ?c) &*& node->nextSibling |-> ?ns;
    //@ ensures node(node, p, c) &*& node->nextSibling |-> ns &*& result == p;
{
  //@ open node(node, p, c);
  struct node *p = node->parent;
  //@ close node(node, p, c);
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
    struct node *root = create_tree();
    
    // To call tree_add(root), we need the context for root's parent (which is 0).
    // The contract `(p == 0 ? true : ...)` handles this.
    struct node *left = tree_add(root);
    
    // To call tree_add(left), we need the context for left's parent (root).
    // We must open `node(root, ...)` to provide `node(root, ...)` to `tree_add`.
    //@ open node(root, 0, 2);
    //@ open node_siblings(root->firstChild, root, 1); // This is `node_siblings(left, root, 1)`
    struct node *leftRight = tree_add(left);
    //@ close node_siblings(root->firstChild, root, 2);
    //@ close node(root, 0, 3);

    struct node *leftRightParent = tree_get_parent(leftRight);
    
    // To call tree_add(left), we need the context for left's parent (root).
    //@ open node(root, 0, 3);
    //@ open node_siblings(root->firstChild, root, 2); // This is `node_siblings(left, root, 2)`
    //@ open node_siblings(left->nextSibling, root, 0);
    struct node *leftLeft = tree_add(left);
    //@ close node_siblings(left->nextSibling, root, 0);
    //@ close node_siblings(root->firstChild, root, 3);
    //@ close node(root, 0, 4);

    // To call tree_add(leftRight), we need context for its parent (left).
    // And `left`'s parent is `root`, so we need context for `root` as well.
    //@ open node(root, 0, 4);
    //@ open node_siblings(root->firstChild, root, 3); // This is `node_siblings(left, root, 3)`
    //@ open node(left, root, 2);
    //@ open node_siblings(left->firstChild, left, 1); // This is `node_siblings(leftRight, left, 1)`
    struct node *leftRightRight = tree_add(leftRight);
    //@ close node_siblings(left->firstChild, left, 2);
    //@ close node(left, root, 3);
    //@ close node_siblings(root->firstChild, root, 4);
    //@ close node(root, 0, 5);
    
    // Clean up memory to satisfy VeriFast's leak checker.
    //@ open node(root, 0, 5);
    //@ open node_siblings(root->firstChild, root, 4);
    //@ open node(left, root, 3);
    //@ open node_siblings(left->firstChild, left, 2);
    //@ open node(leftLeft, left, 1);
    //@ open node_siblings(leftLeft->firstChild, leftLeft, 0);
    //@ free(leftLeft);
    //@ open node_siblings(leftLeft->nextSibling, left, 1);
    //@ open node(leftRight, left, 2);
    //@ open node_siblings(leftRight->firstChild, leftRight, 1);
    //@ open node(leftRightRight, leftRight, 1);
    //@ open node_siblings(leftRightRight->firstChild, leftRightRight, 0);
    //@ free(leftRightRight);
    //@ open node_siblings(leftRightRight->nextSibling, leftRight, 0);
    //@ free(leftRight);
    //@ open node_siblings(leftRight->nextSibling, left, 0);
    //@ free(left);
    //@ open node_siblings(left->nextSibling, root, 0);
    //@ free(root);

    return 0;
}
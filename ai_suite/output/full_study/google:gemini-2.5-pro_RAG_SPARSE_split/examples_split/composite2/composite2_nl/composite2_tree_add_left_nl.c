#include "stdlib.h"
#include "limits.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

// A precise predicate for a single node's data.
// (n, p) are inputs, (l, r, c) are outputs.
predicate node_pred(struct node *n, struct node *p; struct node *l, struct node *r, int c) =
    n->left |-> l &*&
    n->right |-> r &*&
    n->parent |-> p &*&
    n->count |-> c &*&
    malloc_block_node(n);

// A precise predicate for a valid tree structure with correct parent pointers and counts.
// (n, p) are inputs, (c) is output.
predicate tree(struct node *n, struct node *p; int c) =
    n == 0 ?
        c == 0
    :
        node_pred(n, p, ?l, ?r, c) &*&
        tree(l, n, ?lc) &*&
        tree(r, n, ?rc) &*&
        c == 1 + lc + rc &*&
        (l == 0 || l != r);

// A predicate for the "context" of a node 'n', i.e., the path of ancestors from its parent 'p' to the root.
// It owns the ancestor nodes and the sibling subtrees.
// The counts of the ancestors are not constrained.
predicate ancestors_shape(struct node *n, struct node *p) =
    p == 0 ?
        true
    :
        p->parent |-> ?gp &*&
        p->left |-> ?l &*&
        p->right |-> ?r &*&
        p->count |-> _ &*&
        malloc_block_node(p) &*&
        (n == l && n != r ? tree(r, p, _) :
         n == r && n != l ? tree(l, p, _) :
         (n == l && n == r ? tree(l, p, 0) &*& tree(r, p, 0) : false)) &*&
        ancestors_shape(p, gp);

// A predicate representing a fully consistent tree containing a specific node 'n' with parent 'p' and count 'n_count'.
// This predicate owns the entire tree.
predicate tree_and_ancestors(struct node *n, struct node *p, int n_count) =
    p == 0 ?
        tree(n, 0, n_count)
    :
        p->parent |-> ?gp &*&
        p->left |-> ?l &*&
        p->right |-> ?r &*&
        p->count |-> ?p_count &*&
        malloc_block_node(p) &*&
        (
            n == l && n != r ?
                tree(n, p, n_count) &*& tree(r, p, ?r_count) &*& p_count == 1 + n_count + r_count
            : n == r && n != l ?
                tree(l, p, ?l_count) &*& tree(n, p, n_count) &*& p_count == 1 + l_count + n_count
            : n == l && n == r ? // n=l=r=0
                tree(n, p, n_count) &*& tree(r, p, 0) &*& p_count == 1 + n_count &*& n_count == 0
            :
                false
        ) &*&
        tree_and_ancestors(p, gp, p_count);

@*/

/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires tree(node, ?p, ?c);
    //@ ensures tree(node, p, c) &*& result == c;
{
    //@ open tree(node, p, c);
    int result = 0;
    if (node == 0) {
        //@ assert c == 0;
    } else {
        //@ open node_pred(node, p, _, _, c);
        result = node->count;
        //@ close node_pred(node, p, _, _, c);
    }
    //@ close tree(node, p, c);
    return result;
}


/*`fixup_ancestors()` Function:
- Parameters: Takes a node pointer, parent pointer, 
and the new count as input.
- Description: This function updates the count of the
  ancestors of the provided node based on the new count
  provided.
  
It makes sure that the node's count is updated with the given value and the ancestors' count is also updated. */
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires tree(node, parent, count) &*& ancestors_shape(node, parent);
    //@ ensures tree_and_ancestors(node, parent, count);
{
    //@ open ancestors_shape(node, parent);
    if (parent == 0) {
        //@ close tree_and_ancestors(node, 0, count);
    } else {
        //@ assert parent->parent |-> ?grandparent &*& parent->left |-> ?left &*& parent->right |-> ?right;
        //@ assert ancestors_shape(parent, grandparent);
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            //@ assert tree(right, parent, ?rc);
            leftCount = count;
            rightCount = subtree_get_count(right);
            //@ assert rightCount == rc;
        } else if (node == right && node != left) {
            //@ assert tree(left, parent, ?lc);
            leftCount = subtree_get_count(left);
            //@ assert leftCount == lc;
            rightCount = count;
        } else if (node == left && node == right) { // implies node == 0
            //@ assert tree(right, parent, ?rc);
            //@ assert count == 0 && rc == 0;
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else {
            abort();
        }
        // to avoid integer overflow
        if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort();}
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        
        //@ close node_pred(parent, grandparent, left, right, parentCount);
        //@ close tree(parent, grandparent, parentCount);
        
        fixup_ancestors(parent, grandparent, parentCount);
        
        //@ assert tree_and_ancestors(parent, grandparent, parentCount);
        //@ close tree_and_ancestors(node, parent, count);
    }
}


// TODO: make this function pass the verification
/*`tree_add_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function adds a new node
 as the left child of the input node.
 
It makes sure to return the new node in the tree.*/
struct node *tree_add_left(struct node *node)
    //@ requires node_pred(node, ?p, 0, ?r, ?c) &*& tree(r, node, ?rc) &*& c == 1 + rc &*& ancestors_shape(node, p);
    //@ ensures tree_and_ancestors(result, node, 1);
{
    if (node == 0) {
        abort(); // Unreachable under this contract
    }
    {
        struct node *n = malloc(sizeof(struct node));
        if (n == 0) {
            abort();
        }
        n->left = 0;
        n->right = 0;
        n->parent = node;
        n->count = 1;
        //@ close node_pred(n, node, 0, 0, 1);
        //@ close tree(0, n, 0);
        //@ close tree(n, node, 1);
        {
            struct node *nodeLeft = node->left;
            if (nodeLeft != 0) {
                abort(); // Unreachable, node_pred requires node->left |-> 0
            }
            node->left = n;
            if (n == node->right) {
                abort(); // Unreachable, n is a fresh pointer
            }
            //@ close ancestors_shape(n, node);
            fixup_ancestors(n, node, 1);
        }
        return n;
    }
}
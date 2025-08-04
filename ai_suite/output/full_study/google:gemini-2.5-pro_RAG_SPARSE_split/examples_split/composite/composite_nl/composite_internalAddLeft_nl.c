#include "stdlib.h"
#include "limits.h"

/***
 * Description:
 * This program implements a tree structure where each node has pointers to 
 * a left child, a right child, and a parent. Nodes store a `count` representing
 * the number of nodes in the subtree.
 *
 * The tree supports:
 * - Creating a root node.
 * - Adding a left child to a node.
 * - Retrieving the number of nodes in a subtree.
 * - Updating node counts recursively.
 */

/***
 * Structure representing a node in the tree.
 * Each node has a left child, a right child, a parent, and an integer count.
 */
struct Node {
    struct Node* left;
    struct Node* right;
    struct Node* parent;
    int count;
};

/*@

// A tree structure with parent pointers.
// The count of a node is the number of nodes in the subtree rooted at it.
predicate tree(struct Node *n, struct Node *p; int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> c &*&
        malloc_block_Node(n) &*&
        tree(l, n, ?lc) &*& tree(r, n, ?rc) &*&
        c == 1 + lc + rc;

// A spine of ancestors from 'n' upwards.
// This predicate owns the 'parent' and 'count' fields, and the malloc_block of each node on the path.
predicate ancestor_spine(struct Node *n; list<int> counts) =
    n == 0 ?
        counts == nil
    :
        n->parent |-> ?p &*& n->count |-> head(counts) &*&
        malloc_block_Node(n) &*&
        ancestor_spine(p, tail(counts));

fixpoint list<int> increment_all(list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return cons(h + 1, increment_all(t));
    }
}

fixpoint bool all_lt(list<int> xs, int limit) {
    switch (xs) {
        case nil: return true;
        case cons(h, t): return h < limit && all_lt(t, limit);
    }
}

lemma void all_lt_cons(list<int> xs, int limit)
    requires all_lt(xs, limit) == true &*& xs != nil;
    ensures all_lt(tail(xs), limit) == true && head(xs) < limit;
{
    switch (xs) {
        case nil:
        case cons(h, t):
    }
}

@*/


/***
 * Description:
 * The `create` function creates and returns a new tree node with no children.
 *
 * @returns A pointer to a newly allocated `Node`.
 *
 * This function makes sure to return a tree with one node. 
 */
struct Node* create() 
    //@ requires true;
    //@ ensures tree(result, 0, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->parent = 0;
    n->left = 0;
    n->right = 0;
    n->count = 1;
    //@ close tree(0, n, 0);
    //@ close tree(0, n, 0);
    //@ close tree(n, 0, 1);
    return n;
}


/***
 * Description:
 * The `internalCreate` function creates a new node with a given parent.
 *
 * @param parent - A pointer to the parent node.
 *
 * The function makes sure that the returned node is not null and a subtree with that node is linked to the parent.
 */
struct Node* internalCreate(struct Node* parent)
    //@ requires true;
    //@ ensures tree(result, parent, 1);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = parent;
    n->count = 1;
    //@ close tree(0, n, 0);
    //@ close tree(0, n, 0);
    //@ close tree(n, parent, 1);
    return n;
}


/***
 * Description:
 * The `fix` function updates the `count` field of a non-null node and propagates the update to its ancestors.
 *
 * @param node - A pointer to the node whose count should be updated.
 *
 * The function makes sure that the count field of current node with its ancestors is incremented by 1
 */
void fix(struct Node* node)
    //@ requires node != 0 &*& ancestor_spine(node, ?counts) &*& all_lt(counts, INT_MAX) == true;
    //@ ensures ancestor_spine(node, increment_all(counts));
{
    //@ open ancestor_spine(node, counts);
    //@ all_lt_cons(counts, INT_MAX);
    int tmp = node->count;
    if (tmp == INT_MAX) {
        abort();
    }
    node->count = tmp + 1;

    struct Node* parent = node->parent;
    if(parent != 0) {
        fix(parent);
    } else {
        //@ open ancestor_spine(0, tail(counts));
        //@ close ancestor_spine(0, increment_all(tail(counts)));
    }
    //@ close ancestor_spine(node, increment_all(counts));
}


// TODO: make this function pass the verification
/***
 * Description:
 * The `internalAddLeft` function creates and adds a left child to a node.
 *
 * @param node - A pointer to the node where the left child should be added. The node has empty left child.
 *
 * The function makes sure to add a left child to node and updates the `count` field of its ancestors by incrementing by 1.
 */
struct Node* internalAddLeft(struct Node* node)
    /*@ requires node != 0 &*&
                 node->left |-> 0 &*&
                 node->right |-> ?r &*&
                 ancestor_spine(node, ?counts) &*&
                 tree(r, node, ?rc) &*&
                 all_lt(counts, INT_MAX) == true &*&
                 head(counts) == 1 + rc; @*/
    /*@ ensures  tree(result, node, 1) &*&
                 node->left |-> result &*&
                 node->right |-> r &*&
                 ancestor_spine(node, increment_all(counts)) &*&
                 tree(r, node, rc) &*&
                 head(increment_all(counts)) == 1 + 1 + rc; @*/
{
    struct Node* child = internalCreate(node);
    node->left = child;
    fix(node);
    return child;
}
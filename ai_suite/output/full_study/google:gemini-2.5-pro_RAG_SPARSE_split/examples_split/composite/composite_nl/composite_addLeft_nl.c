    predicate tree(struct Node *n; int count, struct Node *p) =
        n == 0 ?
            count == 0
        :
            n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> count &*& malloc_block_Node(n) &*&
            tree(l, ?lc, n) &*& tree(r, ?rc, n) &*&
            count == 1 + lc + rc;
    predicate node_and_subtrees(struct Node *n; struct Node *p, int correct_count) =
        n == 0 ?
            correct_count == 0
        :
            ... n->count |-> _ &*& ...
            tree(n->left, ?lc, n) &*& tree(n->right, ?rc, n) &*&
            correct_count == 1 + lc + rc;
    predicate path_counts_off_by_one(struct Node *n) =
        n == 0 ?
            true
        :
            node_and_subtrees(n, ?p, ?correct_count) &*&
            n->count |-> correct_count - 1 &*&
            path_counts_off_by_one(p);
    predicate path_counts_correct(struct Node *n) =
        n == 0 ?
            true
        :
            node_and_subtrees(n, ?p, ?correct_count) &*&
            n->count |-> correct_count &*&
            path_counts_correct(p);
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
// Predicate for a well-formed tree or subtree.
// `n` is the root of the subtree.
// `count` is the number of nodes in the subtree.
// `p` is the parent of the root `n`.
predicate tree(struct Node *n; int count, struct Node *p) =
    n == 0 ?
        count == 0
    :
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> count &*& malloc_block_Node(n) &*&
        tree(l, ?lc, n) &*& tree(r, ?rc, n) &*&
        count == 1 + lc + rc &*& 1 <= count;

// Predicate for a node and its subtrees, where the subtrees are valid,
// but the count of the node `n` itself is not constrained.
// `correct_count` is the count that `n` *should* have.
predicate node_and_subtrees(struct Node *n; struct Node *p, int correct_count) =
    n == 0 ?
        correct_count == 0
    :
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> _ &*& malloc_block_Node(n) &*&
        tree(l, ?lc, n) &*& tree(r, ?rc, n) &*&
        correct_count == 1 + lc + rc;

// Predicate for a path from `n` to the root where each node's count is one less than it should be.
predicate path_counts_off_by_one(struct Node *n) =
    n == 0 ?
        true
    :
        node_and_subtrees(n, ?p, ?correct_count) &*&
        n->count |-> correct_count - 1 &*&
        path_counts_off_by_one(p);

// Predicate for a path from `n` to the root where each node's count is correct.
predicate path_counts_correct(struct Node *n) =
    n == 0 ?
        true
    :
        node_and_subtrees(n, ?p, ?correct_count) &*&
        n->count |-> correct_count &*&
        path_counts_correct(p);

// Lemma to convert a path with correct counts back into a full tree predicate.
lemma void path_to_tree_lemma(struct Node *n)
    requires path_counts_correct(n);
    ensures tree(n, _, _);
{
    open path_counts_correct(n);
    if (n != 0) {
        open node_and_subtrees(n, ?p, ?correct_count);
        close tree(n, correct_count, p);
    } else {
        close tree(0, 0, _);
    }
}

// Lemma function that models the behavior of the `fix` function.
// It corrects the counts along the ancestor path.
lemma void fix_lemma(struct Node *node)
    requires node != 0 &*& path_counts_off_by_one(node);
    ensures path_counts_correct(node);
{
    open path_counts_off_by_one(node);
    open node_and_subtrees(node, ?p, ?correct_count);
    
    int tmp = node->count;
    if (tmp == INT_MAX) {
        // This path is not taken in our scenario.
        abort();
    }
    node->count = tmp + 1;
    
    if (p != 0) {
        fix_lemma(p);
    } else {
        close path_counts_correct(0);
    }
    
    close node_and_subtrees(node, p, correct_count);
    close path_counts_correct(node);
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
    //@ ensures tree(result, 1, 0);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->parent = 0;
    n->left = 0;
    n->right = 0;
    n->count = 1;
    
    //@ close tree(0, 0, n);
    //@ close tree(0, 0, n);
    //@ close tree(n, 1, 0);
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
    //@ ensures tree(result, 1, parent);
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = parent;
    n->count = 1;

    //@ close tree(0, 0, n);
    //@ close tree(0, 0, n);
    //@ close tree(n, 1, parent);
    return n;
}


/***
 * Description:
 * The `internalAddLeft` function creates and adds a left child to a node.
 *
 * @param node - A pointer to the node where the left child should be added. The node has empty left child.
 *
 * The function makes sure to add a left child to node and updates the `count` field of its ancestors by incrementing by 1.
 */
struct Node* internalAddLeft(struct Node* node)
    //@ requires path_counts_correct(node) &*& node != 0 &*& node->left == 0;
    //@ ensures tree(result, 1, node) &*& tree(node, _, _);
{
    //@ open path_counts_correct(node);
    //@ open node_and_subtrees(node, ?p, ?correct_count);
    //@ assert node->left |-> 0 &*& node->right |-> ?r &*& tree(r, ?rc, node);
    
    struct Node* child = internalCreate(node);
    //@ assert tree(child, 1, node);
    
    node->left = child;
    
    //@ close node_and_subtrees(child, node, 1);
    //@ close path_counts_off_by_one(child);
    
    //@ close node_and_subtrees(node, p, correct_count + 1);
    //@ close path_counts_off_by_one(node);
    
    fix_lemma(node);
    //@ assert path_counts_correct(node);
    
    path_to_tree_lemma(node);
    //@ assert tree(node, _, p);
    
    //@ open tree(node, _, p);
    //@ open tree(child, 1, node);
    //@ close tree(child, 1, node);
    //@ close tree(node, _, p);
    
    return child;
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
    //@ requires path_counts_off_by_one(node) &*& node != 0;
    //@ ensures path_counts_correct(node);
{
    //@ open path_counts_off_by_one(node);
    //@ open node_and_subtrees(node, ?p, ?correct_count);
    
    int tmp = node->count;
    if (tmp == INT_MAX) {
        abort();
    }
    node->count = tmp + 1;

    struct Node* parent = node->parent;
    if(parent != 0) {
        fix(parent);
    } else {
        //@ close path_counts_correct(0);
    }
    
    //@ close node_and_subtrees(node, p, correct_count);
    //@ close path_counts_correct(node);
}


// TODO: make this function pass the verification
/***
 * Description:
 * The `addLeft` function adds a left child to a given node and returns the newly added child.
 *
 * @param node - A pointer to the node where the left child should be added, and its both children are originally empty.
 *
 * The function makes sure that a new (and distinct) left child node is added and returned.
 */
struct Node* addLeft(struct Node* node)
    //@ requires tree(node, 1, ?p);
    //@ ensures tree(result, 1, node) &*& tree(node, 2, p) &*& result != 0 &*& result != node;
{
    //@ open tree(node, 1, p);
    //@ close path_counts_correct(node->parent);
    //@ close node_and_subtrees(node, p, 1);
    //@ close path_counts_correct(node);
    
    struct Node* newChild = internalAddLeft(node);
    
    //@ open tree(node, 2, p);
    //@ assert newChild == node->left;
    //@ close tree(node, 2, p);
    
    return newChild;
}
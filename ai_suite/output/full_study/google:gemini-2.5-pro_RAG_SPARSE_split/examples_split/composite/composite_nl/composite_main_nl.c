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
// Predicate for a well-formed tree (or subtree).
// It is precise, meaning VeriFast can reason more powerfully about it.
// `n`: root of the subtree.
// `p`: parent of the root `n`.
// `c`: number of nodes in the subtree.
predicate tree(struct Node* n, struct Node* p; int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> c &*&
        malloc_block_Node(n) &*&
        tree(l, n, ?cl) &*& tree(r, n, ?cr) &*&
        c == 1 + cl + cr;

// Predicate for the path from a node 'n' up to the root.
// It owns the `parent` and `count` fields of each node on the path.
// `n`: the starting node of the path.
// `counts`: a list of the 'count' values for each node on the path.
predicate path_up(struct Node* n; list<int> counts) =
    n == 0 ?
        counts == nil
    :
        n->parent |-> ?p &*& n->count |-> ?c &*&
        path_up(p, ?p_counts) &*&
        counts == cons(c, p_counts);

// Fixpoint function to increment every element in a list of integers by 1.
fixpoint list<int> add1_to_list(list<int> xs) {
    switch(xs) {
        case nil: return nil;
        case cons(h, t): return cons(h + 1, add1_to_list(t));
    }
}

// Lemma to convert a `tree` predicate into its constituent parts,
// including the `path_up` predicate for its ancestors.
lemma void tree_to_path_up_lemma(struct Node* n)
    requires tree(n, ?p, ?c);
    ensures n == 0 ?
        c == 0
    :
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> c &*&
        malloc_block_Node(n) &*&
        tree(l, n, ?cl) &*& tree(r, n, ?cr) &*&
        c == 1 + cl + cr &*&
        path_up(p, ?p_counts);
{
    open tree(n, p, c);
    if (n != 0) {
        tree_to_path_up_lemma(n->parent);
        close path_up(n, cons(c, _));
    }
}

// Lemma to convert the constituent parts of a tree back into
// a single `tree` predicate.
lemma void path_up_to_tree_lemma(struct Node* n)
    requires
        n == 0 ?
            true
        :
            n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> ?p &*& n->count |-> ?c &*&
            malloc_block_Node(n) &*&
            tree(l, n, ?cl) &*& tree(r, n, ?cr) &*&
            c == 1 + cl + cr &*&
            path_up(p, ?p_counts);
    ensures tree(n, p, c);
{
    if (n != 0) {
        open path_up(n->parent, _);
        path_up_to_tree_lemma(n->parent);
    }
    close tree(n, _, _);
}
@*/

struct Node* internalCreate(struct Node* parent);
void fix(struct Node* node);
struct Node* internalAddLeft(struct Node* node);
int internalGetNbOfNodes(struct Node* n);


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
 * The `addLeft` function adds a left child to a given node and returns the newly added child.
 *
 * @param node - A pointer to the node where the left child should be added, and its both children are originally empty.
 *
 * The function makes sure that a new (and distinct) left child node is added and returned.
 */
struct Node* addLeft(struct Node* node)
    //@ requires tree(node, ?p, ?c) &*& node->left == 0;
    //@ ensures tree(node, p, c + 1) &*& tree(result, node, 1) &*& result == node->left;
{
    //@ open tree(node, p, c);
    //@ tree_to_path_up_lemma(node->parent);
    struct Node* newChild = internalAddLeft(node);
    //@ path_up_to_tree_lemma(node->parent);
    //@ close tree(node, p, c + 1);
    return newChild;
}


/***
 * Description:
 * The `getNbOfNodes` function retrieves the number of nodes in the subtree rooted at `n`.
 *
 * @param n - A pointer to the root of the subtree.
 *
 * The function makes sure not to change the subtree and return the `count` field of the node.
 */
int getNbOfNodes(struct Node* n)
    //@ requires tree(n, ?p, ?c);
    //@ ensures tree(n, p, c) &*& result == c;
{
    int c = internalGetNbOfNodes(n);
    return c;
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
 * The `internalAddLeft` function creates and adds a left child to a node.
 *
 * @param node - A pointer to the node where the left child should be added. The node has empty left child.
 *
 * The function makes sure to add a left child to node and updates the `count` field of its ancestors by incrementing by 1.
 */
struct Node* internalAddLeft(struct Node* node)
    /*@
    requires
        node != 0 &*&
        node->left |-> 0 &*& node->right |-> ?r &*& node->parent |-> ?p &*& node->count |-> ?c &*&
        malloc_block_Node(node) &*&
        tree(r, node, ?cr) &*& c == 1 + cr &*&
        path_up(p, ?p_counts);
    @*/
    /*@
    ensures
        tree(result, node, 1) &*&
        node->left |-> result &*& node->right |-> r &*& node->parent |-> p &*& node->count |-> c + 1 &*&
        malloc_block_Node(node) &*&
        tree(r, node, cr) &*&
        path_up(p, add1_to_list(p_counts));
    @*/
{
    struct Node* child = internalCreate(node);
    node->left = child;
    
    //@ open path_up(node->parent, _);
    //@ close path_up(node, cons(node->count, _));
    fix(node);
    //@ open path_up(node, _);
    
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
    //@ requires node != 0 &*& path_up(node, ?counts);
    //@ ensures path_up(node, add1_to_list(counts));
{
    //@ open path_up(node, counts);
    //@ assert counts == cons(?c, ?p_counts);
    int tmp = node->count;
    if (tmp == INT_MAX) {
        abort();
    }
    node->count = tmp + 1;

    struct Node* parent = node->parent;
    if(parent != 0) {
        fix(parent);
    }
    //@ close path_up(node, add1_to_list(counts));
}


/***
 * Description:
 * The `internalGetNbOfNodes` function returns the number of nodes in the subtree rooted at `n`.
 *
 * @param n - A pointer to the root node.
 *
 * The function simply returns the `count` field of the node.
 */
int internalGetNbOfNodes(struct Node* n)
    //@ requires tree(n, ?p, ?c);
    //@ ensures tree(n, p, c) &*& result == c;
{
    //@ open tree(n, p, c);
    int c_val = n->count;
    //@ close tree(n, p, c);
    return c_val;
}


// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function demonstrates tree operations by:
 * - Creating a root node.
 * - Adding a left child.
 * - Adding another left child to the previous one.
 * - Retrieving and asserting the number of nodes in the subtree.
 */
int main()
    //@ requires true;
    //@ ensures true;
{
    struct Node* mytree = create();
    //@ assert tree(mytree, 0, 1);
    
    //@ open tree(mytree, 0, 1);
    struct Node* child = addLeft(mytree);
    //@ close tree(mytree, 0, 2);
    //@ assert tree(child, mytree, 1);

    //@ open tree(mytree, 0, 2);
    //@ open tree(child, mytree, 1);
    struct Node* child2 = addLeft(child);
    //@ close tree(child, mytree, 2);
    //@ close tree(mytree, 0, 3);
    //@ assert tree(child2, child, 1);
  
    int c = getNbOfNodes(child2);
    assert(c == 1);
    
    //@ open tree(mytree, 0, 3);
    //@ open tree(child, mytree, 2);
    //@ open tree(child2, child, 1);
    //@ open tree(0, child2, 0);
    //@ open tree(0, child2, 0);
    free(child2);
    //@ open tree(0, child, 0);
    free(child);
    //@ open tree(0, mytree, 0);
    free(mytree);
    
    abort();
}
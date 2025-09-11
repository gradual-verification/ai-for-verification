#include "stdlib.h"
#include "assert.h"
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

struct Node {
    struct Node* left;
    struct Node* right;
    struct Node* parent;
    int count;
};

/*@
// Predicate for a node's fields, used for convenience.
predicate node_fields(struct Node* n, struct Node* l, struct Node* r, struct Node* p, int c) =
    n->left |-> l &*&
    n->right |-> r &*&
    n->parent |-> p &*&
    n->count |-> c &*&
    malloc_block_Node(n);

// Forward declaration for mutual recursion with `unfixed_path`.
predicate tree(struct Node *n; struct Node *p, int size);

// Predicate for the path of nodes from `n` to the root whose counts are incorrect.
// `child` is the immediate child of `n` that is on the path towards the modification.
// `child_new_size` is the new, correct size of the subtree at `child`.
predicate unfixed_path(struct Node* n, struct Node* child, int child_new_size) =
    n == 0 ?
        child == 0
    :
        node_fields(n, ?l, ?r, ?p, ?c) &*&
        c < INT_MAX &*&
        (l == child ?
            tree(r, n, ?rsize) &*&
            c == 1 + (child_new_size - 1) + rsize &*&
            unfixed_path(p, n, 1 + child_new_size + rsize)
        :
            r == child ?
                tree(l, n, ?lsize) &*&
                c == 1 + lsize + (child_new_size - 1) &*&
                unfixed_path(p, n, 1 + lsize + child_new_size)
            :
                // This case should not happen in a well-formed path.
                false
        );

// Predicate for a valid tree. It is precise, meaning for a given `n`,
// `p` and `size` are uniquely determined.
predicate tree(struct Node *n; struct Node *p, int size) =
    n == 0 ?
        size == 0
    :
        node_fields(n, ?l, ?r, p, size) &*&
        tree(l, n, ?lsize) &*&
        tree(r, n, ?rsize) &*&
        size == 1 + lsize + rsize &*&
        1 <= size;

@*/


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
 * The `fix` function updates the `count` field of a non-null node and propagates the update to its ancestors.
 *
 * @param node - A pointer to the node whose count should be updated.
 *
 * The function makes sure that the count field of current node with its ancestors is incremented by 1
 */
void fix(struct Node* node)
    //@ requires unfixed_path(node, ?child, ?child_new_size);
    //@ ensures tree(node, _, _);
{
    //@ open unfixed_path(node, child, child_new_size);
    if (node == 0) {
        //@ close tree(0, _, 0);
        return;
    }
    //@ assert node_fields(node, ?l, ?r, ?p, ?c);
    int tmp = node->count;
    if (tmp == INT_MAX) {
        abort();
    }
    node->count = tmp + 1;
    int new_size = tmp + 1;

    struct Node* parent = node->parent;
    if (parent != 0) {
        //@ assert unfixed_path(parent, node, new_size);
        fix(parent);
        //@ assert tree(parent, _, _);
    }

    /*@
    if (l == child) {
        open unfixed_path(child, _, _); // Should be a leaf of the unfixed path.
        close tree(child, node, child_new_size);
    } else {
        open unfixed_path(child, _, _);
        close tree(child, node, child_new_size);
    }
    @*/
    
    //@ if (l == child) { close tree(l, node, child_new_size); }
    //@ if (r == child) { close tree(r, node, child_new_size); }
    
    //@ close tree(node, p, new_size);
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
    //@ requires tree(node, ?p, ?size) &*& node->left |-> 0;
    //@ ensures tree(node, p, size + 1) &*& tree(result, node, 1);
{
    //@ open tree(node, p, size);
    //@ assert node_fields(node, 0, ?r, p, size);
    //@ open tree(0, node, 0);
    //@ assert tree(r, node, ?rsize);
    //@ assert size == 1 + 0 + rsize;

    struct Node* child = internalCreate(node);
    //@ assert tree(child, node, 1);
    node->left = child;

    //@ close unfixed_path(node, child, 1);
    fix(node);
    //@ assert tree(node, p, size + 1);
    
    //@ open tree(node, p, size + 1);
    //@ assert node->left |-> ?new_l;
    //@ assert tree(new_l, node, 1);
    //@ close tree(node, p, size + 1);
    
    return child;
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
    //@ requires tree(node, ?p, 1);
    //@ ensures tree(node, p, 2) &*& tree(result, node, 1) &*& result != node;
{
    //@ open tree(node, p, 1);
    //@ assert node->left |-> 0;
    //@ close tree(node, p, 1);
    struct Node* newChild = internalAddLeft(node);
    return newChild;
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
    //@ requires tree(n, ?p, ?size);
    //@ ensures tree(n, p, size) &*& result == size;
{
    //@ open tree(n, p, size);
    int c = n->count;
    //@ close tree(n, p, size);
    return c;
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
    //@ requires tree(n, ?p, ?size);
    //@ ensures tree(n, p, size) &*& result == size;
{
    int c = internalGetNbOfNodes(n);
    return c;
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
    
    struct Node* child = addLeft(mytree);
    //@ assert tree(mytree, 0, 2) &*& tree(child, mytree, 1);
    
    //@ open tree(mytree, 0, 2);
    //@ assert tree(child, mytree, 1);
    struct Node* child2 = addLeft(child);
    //@ assert tree(child, mytree, 2) &*& tree(child2, child, 1);
    //@ close tree(mytree, 0, 3);
  
    int c = getNbOfNodes(child2);
    //@ assert tree(child2, child, 1) &*& c == 1;
    assert(c == 1);
    
    // Clean up memory to avoid leaks in verification, although the program aborts.
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
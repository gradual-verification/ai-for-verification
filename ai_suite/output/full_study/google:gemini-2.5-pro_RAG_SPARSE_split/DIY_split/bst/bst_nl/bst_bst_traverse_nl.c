#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@

predicate bst(struct bst_node *node, int min, int max; list<int> vs) =
    node == 0 ?
        vs == nil
    :
        node->left |-> ?l &*&
        node->right |-> ?r &*&
        node->value |-> ?v &*&
        malloc_block_bst_node(node) &*&
        min < v &*& v < max &*&
        bst(l, min, v, ?lvs) &*&
        bst(r, v, max, ?rvs) &*&
        vs == append(lvs, cons(v, rvs)) &*&
        distinct(vs) == true;

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `bst_traverse` function traverses the subtree of a given node.
 *
 * @param node: the node to be traversed on, which is a root of a bst
 *
 * The function makes sure that the given node is still a root of a bst. 
 */
void bst_traverse(struct bst_node *node)
    //@ requires [?f]bst(node, ?min, ?max, ?vs);
    //@ ensures [f]bst(node, min, max, vs);
{
    if (node == 0) {
        // Base case: The tree is empty. The bst predicate holds trivially.
    } else {
        //@ open [f]bst(node, min, max, vs);
        int val = node->value;
        bst_traverse(node->left);
        bst_traverse(node->right);
        //@ close [f]bst(node, min, max, vs);
    }
}
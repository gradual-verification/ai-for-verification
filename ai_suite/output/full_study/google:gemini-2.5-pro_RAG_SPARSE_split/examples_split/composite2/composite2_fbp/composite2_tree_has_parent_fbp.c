#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate subtree(struct node *root, struct node *parent, int count) =
        root == 0 ?
            count == 0
        :
            root->left |-> ?left &*& root->right |-> ?right &*& root->parent |-> parent &*& root->count |-> count &*& malloc_block_node(root) &*&
            subtree(left, root, ?leftCount) &*& subtree(right, root, ?rightCount) &*& count == 1 + leftCount + rightCount;

predicate context(struct node *node, struct node *parent, int count) = 
        parent == 0 ?
            true
        :
            parent->left |-> ?left &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*& malloc_block_node(parent) &*&
            context(parent, grandparent, parentCount) &*&
            (node == left ? 
                 subtree(right, parent, ?rightCount) &*& parentCount == 1 + count + rightCount
             :
                 node == right &*& subtree(left, parent, ?leftCount) &*& parentCount == 1 + count + leftCount
            );

predicate tree(struct node *node) = 
    context(node, ?parent, ?count) &*& subtree(node, parent, count);
@*/



// TODO: make this function pass the verification
bool tree_has_parent(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(node);
{
    //@ open tree(node);
    //@ open subtree(node, ?p, ?c);
    bool result = false;
    if (node == 0) {
        // If node is null, it has no parent. `result` remains false.
        // From `open subtree(0, p, c)`, VeriFast knows that `c == 0`.
    } else {
        // If node is not null, `open subtree` gives us access to its fields.
        // We have `node->parent |-> p`.
        struct node *parent = node->parent;
        result = parent != 0;
    }
    //@ close subtree(node, p, c);
    //@ close tree(node);
    return result;
}
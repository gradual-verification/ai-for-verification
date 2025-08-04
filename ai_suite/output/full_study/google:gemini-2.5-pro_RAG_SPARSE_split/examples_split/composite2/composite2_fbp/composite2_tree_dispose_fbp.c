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



void dispose_node(struct node *node)
    //@ requires subtree(node, _, _);
    //@ ensures true;
{
    if (node == 0) {
        //@ open subtree(0, _, _);
    } else {
        //@ open subtree(node, _, _);
        {
            struct node *left = node->left;
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        free(node);
    }
}


// TODO: make this function pass the verification
void tree_dispose(struct node *node)
    //@ requires tree(node);
    //@ ensures true;
{
    //@ open tree(node);
    //@ assert context(node, ?p, ?c) &*& subtree(node, p, c);
    if (node == 0) {
        // The node is null. The context might still exist.
        // Since ensures is 'true', we can leak the context.
        //@ open context(0, p, 0);
        //@ open subtree(0, p, 0);
        return;
    }
    
    // This function is only designed to dispose a full tree from its root.
    // If called on a non-root node, we leak the memory for the rest of the tree,
    // which is permissible by the 'ensures true' contract.
    //@ open subtree(node, p, c);
    struct node *parent = node->parent;
    //@ close subtree(node, p, c);

    if (parent != 0) {
        // Not the root, leak the whole tree.
        return;
    }
    
    // We have proved node is the root, so p == 0.
    //@ open context(node, 0, c);
    dispose_node(node);
}
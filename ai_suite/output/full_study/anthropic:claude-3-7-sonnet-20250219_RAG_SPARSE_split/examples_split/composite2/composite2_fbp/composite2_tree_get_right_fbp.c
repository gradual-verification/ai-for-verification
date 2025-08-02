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

struct node *tree_get_right(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    if (node == 0) {
        abort();
    }
    //@ open tree(node);
    //@ open subtree(node, ?parent, ?count);
    struct node *right = node->right;
    //@ close subtree(node->left, node, ?leftCount);
    //@ close subtree(node, parent, count);
    
    //@ assert right |-> ?rightNode;
    //@ assert subtree(right, node, ?rightCount);
    
    //@ open context(node, parent, count);
    //@ if (parent != 0) {
    //@     if (node == parent->left) {
    //@         close context(right, node, rightCount);
    //@     } else {
    //@         close context(right, node, rightCount);
    //@     }
    //@ } else {
    //@     close context(right, node, rightCount);
    //@ }
    
    //@ close tree(right);
    return right;
}
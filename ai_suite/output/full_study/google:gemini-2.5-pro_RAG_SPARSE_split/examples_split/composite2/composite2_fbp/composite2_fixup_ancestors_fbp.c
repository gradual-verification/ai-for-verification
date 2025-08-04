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



int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?parent, ?count);
    //@ ensures subtree(node, parent, count) &*& result == count;
{
    int result = 0;
    //@ open subtree(node, parent, count);
    if (node == 0) {
    } else {
        result = node->count;
    }
    //@ close subtree(node, parent, count);
    return result;
}


// TODO: make this function pass the verification
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires context(node, parent, ?oldCount);
    //@ ensures context(node, parent, count);
{
    //@ open context(node, parent, oldCount);
    if (parent == 0) {
        //@ close context(node, 0, count);
    } else {
        /*@
        assert parent->left |-> ?left &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount_old &*& malloc_block_node(parent) &*&
            context(parent, grandparent, parentCount_old) &*&
            (node == left ? 
                 subtree(right, parent, ?rightCount_old) &*& parentCount_old == 1 + oldCount + rightCount_old
             :
                 node == right &*& subtree(left, parent, ?leftCount_old) &*& parentCount_old == 1 + oldCount + leftCount_old
            );
        @*/
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        
        // The original C code is buggy when a parent has two null children, as it would abort.
        // The conditions are simplified to correctly handle all cases.
        if (node == left) {
            //@ assert subtree(right, parent, ?rightCount_old);
            leftCount = count;
            rightCount = subtree_get_count(right);
            //@ assert rightCount == rightCount_old;
        } else if (node == right) {
            //@ assert subtree(left, parent, ?leftCount_old);
            leftCount = subtree_get_count(left);
            //@ assert leftCount == leftCount_old;
            rightCount = count;
        } else {
            // This branch is unreachable because the context predicate implies
            // that 'node' is either the left or the right child of 'parent'.
            abort();
        }
        
        // to avoid integer overflow
        if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort();}
        
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        
        fixup_ancestors(parent, grandparent, parentCount);
        
        //@ close context(node, parent, count);
    }
}
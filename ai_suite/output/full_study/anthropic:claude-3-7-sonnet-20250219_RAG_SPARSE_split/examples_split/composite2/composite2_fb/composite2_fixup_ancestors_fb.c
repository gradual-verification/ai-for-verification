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
            root->left |-> ?left &*& root->right |-> ?right &*& root->parent |-> parent &*& root->count |-> count &*&
            subtree(left, root, ?leftCount) &*& subtree(right, root, ?rightCount) &*& count == 1 + leftCount + rightCount;

predicate context(struct node *node, struct node *parent, int count) = 
        parent == 0 ?
            true
        :
            parent->left |-> ?left &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*&
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
    if (node == 0) {
    } else {
        result = node->count;
    }
    return result;
}


// TODO: make this function pass the verification
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires context(node, parent, ?oldCount);
    //@ ensures context(node, parent, count);
{
    if (parent == 0) {
        // Base case: no parent to update
    } else {
        // Get parent's fields
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        
        // Calculate new counts
        int leftCount = 0;
        int rightCount = 0;
        
        // Open the context predicate to access parent's fields
        //@ open context(node, parent, oldCount);
        
        if (node == left && node != right) {
            // Node is the left child
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else if (node == right && node != left) {
            // Node is the right child
            leftCount = subtree_get_count(left);
            rightCount = count;
        } else {
            abort();
        }
        
        // Check for integer overflow
        if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
        
        // Calculate parent's new count
        int parentCount = 1 + leftCount + rightCount;
        
        // Update parent's count
        parent->count = parentCount;
        
        // Recursively update ancestors
        //@ close context(node, parent, count);
        fixup_ancestors(parent, grandparent, parentCount);
    }
}
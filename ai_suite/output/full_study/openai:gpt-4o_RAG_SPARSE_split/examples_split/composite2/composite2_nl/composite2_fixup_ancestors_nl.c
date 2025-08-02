#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate tree(struct node *node, struct node *parent, int count) =
    node == 0 ?
        count == 0
    :
        node->parent |-> parent &*&
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->count |-> count &*&
        malloc_block_node(node) &*&
        tree(left, node, ?leftCount) &*&
        tree(right, node, ?rightCount) &*&
        count == 1 + leftCount + rightCount;

@*/

int subtree_get_count(struct node *node)
    //@ requires tree(node, ?parent, ?count);
    //@ ensures tree(node, parent, count) &*& result == count;
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
    //@ requires tree(node, parent, ?nodeCount) &*& tree(parent, ?grandparent, ?parentCount);
    //@ ensures tree(node, parent, count) &*& tree(parent, grandparent, ?newParentCount);
{
    if (parent == 0) {
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else if (node == right && node != left) {
            leftCount = subtree_get_count(left);
            rightCount = count;
        } else {
            abort();
        }
        // to avoid integer overflow
        if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort(); }
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        //@ open tree(parent, grandparent, parentCount);
        //@ close tree(parent, grandparent, parentCount);
        fixup_ancestors(parent, grandparent, parentCount);
    }
}
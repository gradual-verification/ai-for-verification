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
struct node *tree_get_right(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    if (node == 0) {
        //@ open tree(0);
        //@ open subtree(0, ?p, ?c);
        //@ open context(0, p, c);
        abort();
    }
    
    //@ open tree(node);
    //@ open subtree(node, ?parent, ?count);
    // After opening subtree, we have:
    // context(node, parent, count) &*&
    // node->left |-> ?left &*& node->right |-> ?right &*& node->parent |-> parent &*& node->count |-> count &*& malloc_block_node(node) &*&
    // subtree(left, node, ?leftCount) &*& subtree(right, node, ?rightCount) &*&
    // count == 1 + leftCount + rightCount
    
    struct node *right = node->right;
    
    // We want to prove tree(right).
    // tree(right) is defined as: context(right, node, rightCount) &*& subtree(right, node, rightCount).
    
    // We already have subtree(right, node, rightCount).
    
    // We need to construct context(right, node, rightCount).
    // The definition of context(c, p, cc) for p != 0 is:
    //   p->left |-> ?l &*& p->right |-> ?r &*& p->parent |-> ?gp &*& p->count |-> ?pc &*& malloc_block_node(p) &*&
    //   context(p, gp, pc) &*&
    //   (c == l ? ... : c == r &*& subtree(l, p, ?lc) &*& pc == 1 + cc + lc)
    //
    // In our case, c=right, p=node, cc=rightCount.
    // We have all the required chunks from opening tree(node) and subtree(node, ...).
    // Specifically, we have:
    // - node->left |-> left
    // - node->right |-> right
    // - node->parent |-> parent
    // - node->count |-> count
    // - malloc_block_node(node)
    // - context(node, parent, count)
    // - subtree(left, node, leftCount)
    // - The equality `count == 1 + leftCount + rightCount` which matches `pc == 1 + cc + lc`.
    
    //@ close context(right, node, rightCount);
    
    // Now we have context(right, node, rightCount) and subtree(right, node, rightCount).
    
    //@ close tree(right);
    
    return right;
}
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

struct node *tree_get_parent(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    if (node == 0) {
        abort();
    }
    {
        //@ open tree(node);
        //@ open subtree(node, ?parent, ?count);
        struct node *parent = node->parent;
        if (parent == 0) {
            abort();
        }
        //@ close subtree(node, parent, count);
        //@ open context(node, parent, count);
        //@ assert parent->left |-> ?left;
        //@ assert parent->right |-> ?right;
        //@ assert parent->parent |-> ?grandparent;
        //@ assert parent->count |-> ?parentCount;
        
        //@ if (node == left) {
        //@     assert subtree(right, parent, ?rightCount);
        //@     assert parentCount == 1 + count + rightCount;
        //@ } else {
        //@     assert node == right;
        //@     assert subtree(left, parent, ?leftCount);
        //@     assert parentCount == 1 + count + leftCount;
        //@ }
        
        //@ close subtree(parent, grandparent, parentCount);
        //@ close tree(parent);
        return parent;
    }
}
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



// TODO: make this function pass the verification
struct node *tree_get_parent(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    //@ open tree(node);
    if (node == 0) {
        // A null node is considered a valid (empty) tree, but it has no parent.
        abort();
    }
    {
        //@ open subtree(node, _, _);
        struct node *parent = node->parent;
        if (parent == 0) {
            // The node is the root of the tree, so it has no parent.
            //@ close subtree(node, 0, _);
            //@ close tree(node);
            abort();
        }
        
        // Re-assemble the subtree chunk for the current node.
        //@ close subtree(node, parent, _);
        
        // Unfold the context of the current node to get information about its parent.
        // This gives us the context of the parent, the parent's fields, and the sibling's subtree.
        //@ open context(node, parent, _);
        
        // We now have all the pieces to assemble the parent's subtree:
        // - The parent's fields (from opening the context).
        // - The current node's subtree (which we have).
        // - The sibling's subtree (from opening the context).
        //@ close subtree(parent, _, _);
        
        // We have the parent's context and its re-assembled subtree, so we can form the parent's tree.
        //@ close tree(parent);
        
        return parent;
    }
}
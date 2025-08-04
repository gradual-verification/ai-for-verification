#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

inductive tree = empty | tree(struct node *, tree, tree);

fixpoint int tree_count(tree nodes) {
    switch (nodes) {
        case empty: return 0;
        case tree(root, leftNodes, rightNodes): return 1 + tree_count(leftNodes) + tree_count(rightNodes);
    }
}

predicate subtree(struct node *root, struct node *parent, tree nodes)
    =
        switch (nodes) {
            case empty: return root == 0;
            case tree(root0, leftNodes, rightNodes):
                return
                    root == root0 &*&
                    root->left |-> ?left &*& root->right |-> ?right &*& root->parent |-> parent &*& root->count |-> tree_count(nodes) &*&
                    subtree(left, root, leftNodes) &*& subtree(right, root, rightNodes);
        };

inductive context = root | left_context(context, struct node *, tree) | right_context(context, struct node *, tree);

predicate context(struct node *node, struct node *parent, int count, context nodes)
    =
        switch (nodes) {
            case root: return parent == 0;
            case left_context(parentContextNodes, parent0, rightNodes):
                return
                    parent == parent0 &*&
                    parent->left |-> node &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*&
                    context(parent, grandparent, parentCount, parentContextNodes) &*& subtree(right, parent, rightNodes) &*&
                    parentCount == 1 + count + tree_count(rightNodes);
            case right_context(parentContextNodes, parent0, leftNodes):
                return
                    parent == parent0 &*&
                    parent->left |-> ?left &*& parent->right |-> node &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*&
                    context(parent, grandparent, parentCount, parentContextNodes) &*& subtree(left, parent, leftNodes) &*&
                    parentCount == 1 + tree_count(leftNodes) + count;
        };

predicate tree(struct node *node, context contextNodes, tree subtreeNodes)
    = context(node, ?parent, tree_count(subtreeNodes), contextNodes) &*& subtree(node, parent, subtreeNodes);

@*/



// TODO: make this function pass the verification
bool tree_has_parent(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes) &*& subtreeNodes != empty;
    //@ ensures tree(node, contextNodes, subtreeNodes) &*& result == (contextNodes != root);
{
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?p, subtreeNodes);
    
    /*@
    switch (contextNodes) {
        case root:
            open context(node, p, tree_count(subtreeNodes), root);
            // By definition of context(..., root), we have p == 0.
            // The function will return (0 != 0) == false.
            // The spec requires result == (root != root) == false. This matches.
            close context(node, p, tree_count(subtreeNodes), root);
        case left_context(pc, p0, rn):
            open context(node, p, tree_count(subtreeNodes), contextNodes);
            // By definition of context(..., left_context(...)), we have p == p0 and p0 is a valid pointer, so p != 0.
            // The function will return (p != 0) == true.
            // The spec requires result == (left_context(...) != root) == true. This matches.
            close context(node, p, tree_count(subtreeNodes), contextNodes);
        case right_context(pc, p0, ln):
            open context(node, p, tree_count(subtreeNodes), contextNodes);
            // By definition of context(..., right_context(...)), we have p == p0 and p0 is a valid pointer, so p != 0.
            // The function will return (p != 0) == true.
            // The spec requires result == (right_context(...) != root) == true. This matches.
            close context(node, p, tree_count(subtreeNodes), contextNodes);
    }
    @*/

    struct node *parent1 = node->parent;
    
    //@ close subtree(node, p, subtreeNodes);
    //@ close tree(node, contextNodes, subtreeNodes);
    
    return parent1 != 0;
}
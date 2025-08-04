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
                    root == root0 &*& root != 0 &*&
                    root->left |-> ?left &*& root->right |-> ?right &*& root->parent |-> parent &*& root->count |-> tree_count(nodes) &*& malloc_block_node(root) &*&
                    subtree(left, root, leftNodes) &*& subtree(right, root, rightNodes);
        };

inductive context = root | left_context(context, struct node *, tree) | right_context(context, struct node *, tree);

predicate context(struct node *node, struct node *parent, int count, context nodes)
    =
        switch (nodes) {
            case root: return parent == 0;
            case left_context(parentContextNodes, parent0, rightNodes):
                return
                    parent == parent0 &*& parent != 0 &*&
                    parent->left |-> node &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*& malloc_block_node(parent) &*&
                    context(parent, grandparent, parentCount, parentContextNodes) &*& subtree(right, parent, rightNodes) &*&
                    parentCount == 1 + count + tree_count(rightNodes);
            case right_context(parentContextNodes, parent0, leftNodes):
                return
                    parent == parent0 &*& parent != 0 &*&
                    parent->left |-> ?left &*& parent->right |-> node &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*& malloc_block_node(parent) &*&
                    context(parent, grandparent, parentCount, parentContextNodes) &*& subtree(left, parent, leftNodes) &*&
                    parentCount == 1 + tree_count(leftNodes) + count;
        };

predicate tree(struct node *node, context contextNodes, tree subtreeNodes)
    = context(node, ?parent, tree_count(subtreeNodes), contextNodes) &*& subtree(node, parent, subtreeNodes);

@*/



// TODO: make this function pass the verification
struct node *tree_get_right(struct node *node)
    /*@ requires tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return rightNodes != empty;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes):
                   return tree(result, right_context(contextNodes, node, leftNodes), rightNodes);
            };
    @*/
{
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?parent, subtreeNodes);
    /*@
    switch (subtreeNodes) {
        case empty:
            // This case is ruled out by the precondition.
        case tree(node0, leftNodes, rightNodes):
            // We need to build tree(node->right, right_context(contextNodes, node, leftNodes), rightNodes).
            // This expands to:
            //   context(node->right, ?p, tree_count(rightNodes), right_context(contextNodes, node, leftNodes)) &*&
            //   subtree(node->right, p, rightNodes)
            
            // The `subtree` part is already available from opening `subtree(node, ...)`.
            // We need to construct the new `context`.
            close context(node->right, node, tree_count(rightNodes), right_context(contextNodes, node, leftNodes));
            
            // Now, we can construct the final `tree` predicate.
            close tree(node->right, right_context(contextNodes, node, leftNodes), rightNodes);
    }
    @*/
    struct node *right = node->right;
    return right;
}
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
struct node *tree_get_parent(struct node *node)
    /*@ requires
            tree(node, ?contextNodes, ?subtreeNodes) &*& contextNodes != root &*& subtreeNodes != empty;
    @*/
    /*@ ensures
            switch (contextNodes) {
                case root: return false;
                case left_context(parentContextNodes, parent, rightNodes):
                    return result == parent &*& tree(parent, parentContextNodes, tree(parent, subtreeNodes, rightNodes));
                case right_context(parentContextNodes, parent, leftNodes):
                    return result == parent &*& tree(parent, parentContextNodes, tree(parent, leftNodes, subtreeNodes));
            };
    @*/
{
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?p, subtreeNodes);
    struct node *parent = node->parent;
    //@ switch (contextNodes) {
    //@     case root:
    //@     case left_context(parentContextNodes, parent_node, rightNodes):
    //@         open context(node, p, tree_count(subtreeNodes), contextNodes);
    //@         // We have all the chunks for parent_node. We can re-assemble the tree from its point of view.
    //@         close subtree(parent_node, ?grandparent, tree(parent_node, subtreeNodes, rightNodes));
    //@         close tree(parent_node, parentContextNodes, tree(parent_node, subtreeNodes, rightNodes));
    //@     case right_context(parentContextNodes, parent_node, leftNodes):
    //@         open context(node, p, tree_count(subtreeNodes), contextNodes);
    //@         // We have all the chunks for parent_node. We can re-assemble the tree from its point of view.
    //@         close subtree(parent_node, ?grandparent, tree(parent_node, leftNodes, subtreeNodes));
    //@         close tree(parent_node, parentContextNodes, tree(parent_node, leftNodes, subtreeNodes));
    //@ }
    return parent;
}
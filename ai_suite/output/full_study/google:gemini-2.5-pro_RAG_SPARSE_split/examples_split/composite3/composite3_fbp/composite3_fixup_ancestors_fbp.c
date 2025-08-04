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



int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?parent, ?nodes);
    //@ ensures subtree(node, parent, nodes) &*& result == tree_count(nodes);
{
    //@ open subtree(node, parent, nodes);
    int result = 0;
    if (node == 0) {
        //@ assert nodes == empty;
    } else {
        //@ assert nodes == tree(node, _, _);
        result = node->count;
    }
    //@ close subtree(node, parent, nodes);
    return result;
}


// TODO: make this function pass the verification
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires context(node, parent, _, ?contextNodes);
    //@ ensures context(node, parent, count, contextNodes);
{
    //@ open context(node, parent, ?oldCount, contextNodes);
    if (parent == 0) {
        //@ close context(node, 0, count, root);
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            //@ switch(contextNodes) { case root: assert false; case right_context: assert false; case left_context(parentContextNodes, parent0, rightNodes): }
            leftCount = count;
            rightCount = subtree_get_count(right);
            //@ assert rightCount == tree_count(rightNodes);
        } else if (node == right && node != left) {
            //@ switch(contextNodes) { case root: assert false; case left_context: assert false; case right_context(parentContextNodes, parent0, leftNodes): }
            leftCount = subtree_get_count(left);
            //@ assert leftCount == tree_count(leftNodes);
            rightCount = count;
        } else {
            abort();
        }
        {
            if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            
            //@ switch(contextNodes) {
            //@     case root:
            //@         assert false;
            //@         break;
            //@     case left_context(parentContextNodes, parent0, rightNodes):
            //@         assert parentCount == 1 + count + tree_count(rightNodes);
            //@         fixup_ancestors(parent, grandparent, parentCount);
            //@         close context(node, parent, count, contextNodes);
            //@         break;
            //@     case right_context(parentContextNodes, parent0, leftNodes):
            //@         assert parentCount == 1 + tree_count(leftNodes) + count;
            //@         fixup_ancestors(parent, grandparent, parentCount);
            //@         close context(node, parent, count, contextNodes);
            //@         break;
            //@ }
        }
    }
}
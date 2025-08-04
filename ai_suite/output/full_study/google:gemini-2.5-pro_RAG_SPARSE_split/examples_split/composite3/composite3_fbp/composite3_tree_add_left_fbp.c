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
    int result = 0;
    //@ open subtree(node, parent, nodes);
    if (node == 0) {
        //@ switch(nodes) { case empty: case tree(r, l, ri): }
    } else {
        //@ switch(nodes) { case empty: case tree(r, l, ri): }
        result = node->count;
    }
    //@ close subtree(node, parent, nodes);
    return result;
}


void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires context(node, parent, _, ?contextNodes);
    //@ ensures context(node, parent, count, contextNodes);
{
    //@ open context(node, parent, _, contextNodes);
    if (parent == 0) {
        //@ switch(contextNodes) { case root: case left_context(pc, p0, rn): case right_context(pc, p0, ln): }
    } else {
        //@ switch(contextNodes) { case root: case left_context(pc, p0, rn): case right_context(pc, p0, ln): }
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
        {
            if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            fixup_ancestors(parent, grandparent, parentCount);
        }
    }
    //@ close context(node, parent, count, contextNodes);
}


// TODO: make this function pass the verification
struct node *tree_add_left(struct node *node)
    /*@ requires
            tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return leftNodes == empty;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, left_context(contextNodes, node, rightNodes), tree(result, empty, empty));
            };
    @*/
{
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ switch (subtreeNodes) { case empty: return false; case tree(node0, leftNodes, rightNodes): }
    //@ open subtree(node, ?parent, subtreeNodes);
    
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    //@ close subtree(0, n, empty);
    //@ close subtree(0, n, empty);
    //@ close subtree(n, node, tree(n, empty, empty));
    
    {
        struct node *nodeLeft = node->left;
        //@ assert nodeLeft == 0;
        node->left = n;
        
        // The count of the subtree at 'node' has changed.
        // We must update node->count and then fix the counts of all ancestors.
        struct node *right_ptr = node->right;
        int rightCount = subtree_get_count(right_ptr);
        
        if (rightCount < 0 || 1 > INT_MAX - 1 - rightCount) { abort(); }
        int new_node_count = 1 + 1 + rightCount;
        node->count = new_node_count;
        
        struct node *p = node->parent;
        fixup_ancestors(node, p, new_node_count);
        
        //@ close context(n, node, 1, left_context(contextNodes, node, rightNodes));
        //@ close tree(n, left_context(contextNodes, node, rightNodes), tree(n, empty, empty));
    }
    return n;
}
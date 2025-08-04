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



struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, root, tree(result, empty, empty));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close subtree(0, n, empty);
    //@ close subtree(0, n, empty);
    //@ close subtree(n, 0, tree(n, empty, empty));
    //@ close context(n, 0, 1, root);
    //@ close tree(n, root, tree(n, empty, empty));
    return n;
}


int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?parent, ?nodes);
    //@ ensures subtree(node, parent, nodes) &*& result == tree_count(nodes);
{
    int result = 0;
    //@ open subtree(node, parent, nodes);
    if (node == 0) {
        //@ switch(nodes) { case empty: {} case tree(r, l, ri): {}}
    } else {
        //@ switch(nodes) { case empty: {} case tree(r, l, ri): {}}
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
        //@ switch(contextNodes) { case root: {} case left_context(pc, p, r): {} case right_context(pc, p, l): {}}
    } else {
        //@ switch(contextNodes) { case root: {} case left_context(pc, p, r): {} case right_context(pc, p, l): {}}
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
    //@ open subtree(node, ?p, subtreeNodes);
    //@ switch(subtreeNodes) { case empty: {} case tree(n0, l, r): {}}
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    {
        struct node *nodeLeft = node->left;
        node->left = n;
        //@ close subtree(0, n, empty);
        //@ close subtree(0, n, empty);
        //@ close subtree(n, node, tree(n, empty, empty));
        //@ int old_parent_count = 1 + tree_count(l) + tree_count(r);
        //@ open context(node, p, old_parent_count, contextNodes);
        //@ close context(n, node, 1, left_context(contextNodes, node, r));
        fixup_ancestors(n, node, 1);
        //@ close tree(n, left_context(contextNodes, node, r), tree(n, empty, empty));
    }
    return n;
}


struct node *tree_add_right(struct node *node)
    /*@ requires
            tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return rightNodes == empty;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, right_context(contextNodes, node, leftNodes), tree(result, empty, empty));
            };
    @*/
{
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?p, subtreeNodes);
    //@ switch(subtreeNodes) { case empty: {} case tree(n0, l, r): {}}
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    {
        struct node *nodeRight = node->right;
        node->right = n;
        //@ close subtree(0, n, empty);
        //@ close subtree(0, n, empty);
        //@ close subtree(n, node, tree(n, empty, empty));
        //@ int old_parent_count = 1 + tree_count(l) + tree_count(r);
        //@ open context(node, p, old_parent_count, contextNodes);
        //@ close context(n, node, 1, right_context(contextNodes, node, l));
        fixup_ancestors(n, node, 1);
        //@ close tree(n, right_context(contextNodes, node, l), tree(n, empty, empty));
    }
    return n;
}


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
    //@ open context(node, ?p, _, contextNodes);
    //@ switch(contextNodes) { case root: {} case left_context(pc, pa, r): { close tree(pa, pc, tree(pa, subtreeNodes, r)); } case right_context(pc, pa, l): { close tree(pa, pc, tree(pa, l, subtreeNodes)); }}
    struct node *parent = node->parent;
    return parent;
}


void dispose_node(struct node *node)
    //@ requires subtree(node, _, ?nodes);
    //@ ensures true;
{
    //@ open subtree(node, _, nodes);
    if (node == 0) {
        //@ switch(nodes) { case empty: {} case tree(r, l, ri): {}}
    } else {
        //@ switch(nodes) { case empty: {} case tree(r, l, ri): {}}
        {
            struct node *left = node->left;
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        free(node);
    }
}


void tree_dispose(struct node *node)
    //@ requires tree(node, root, ?nodes);
    //@ ensures true;
{
    //@ open tree(node, root, nodes);
    //@ open context(node, ?p, _, root);
    dispose_node(node);
}


// TODO: make this function pass the verification
int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *node0 = create_tree();
    struct node *node = node0;

    //@ open tree(node, ?c0, ?s0);
    //@ switch(s0) { case empty: {} case tree(r, l, ri): {}}
    //@ close tree(node, c0, s0);
    node = tree_add_left(node);

    //@ open tree(node, ?c1, ?s1);
    //@ switch(s1) { case empty: {} case tree(r, l, ri): {}}
    //@ close tree(node, c1, s1);
    node = tree_add_right(node);

    //@ open tree(node, ?c2, ?s2);
    //@ switch(c2) { case root: {} case left_context(pc, p, r): {} case right_context(pc, p, l): {}}
    //@ close tree(node, c2, s2);
    node = tree_get_parent(node);

    //@ open tree(node, ?c3, ?s3);
    //@ switch(s3) { case empty: {} case tree(r, l, ri): {}}
    //@ close tree(node, c3, s3);
    node = tree_add_left(node);

    //@ open tree(node, ?c4, ?s4);
    //@ switch(c4) { case root: {} case left_context(pc, p, r): {} case right_context(pc, p, l): {}}
    //@ close tree(node, c4, s4);
    node = tree_get_parent(node);

    //@ open tree(node, ?c5, ?s5);
    //@ switch(c5) { case root: {} case left_context(pc, p, r): {} case right_context(pc, p, l): {}}
    //@ close tree(node, c5, s5);
    node = tree_get_parent(node);

    //@ open tree(node, ?c6, ?s6);
    //@ close tree(node, c6, s6);
    tree_dispose(node);
    return 0;
}
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
    } else {
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
        //@ close context(node, 0, count, root);
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        //@ switch(contextNodes) { case root: case left_context(pc, p, rns): case right_context(pc, p, lns): }
        if (node == left && node != right) {
            leftCount = count;
            //@ assert contextNodes == left_context(?pc, parent, ?rns);
            rightCount = subtree_get_count(right);
        } else if (node == right && node != left) {
            //@ assert contextNodes == right_context(?pc, parent, ?lns);
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
        //@ close context(node, parent, count, contextNodes);
    }
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
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?p, subtreeNodes);
    //@ switch(subtreeNodes) { case empty: case tree(n0, lns, rns): }
    {
        struct node *nodeLeft = node->left;
        node->left = n;
        //@ close subtree(0, n, empty);
        //@ close subtree(0, n, empty);
        //@ close subtree(n, node, tree(n, empty, empty));
        //@ close context(n, node, 1, left_context(contextNodes, node, rns));
        fixup_ancestors(n, node, 1);
        //@ close tree(n, left_context(contextNodes, node, rns), tree(n, empty, empty));
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
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?p, subtreeNodes);
    //@ switch(subtreeNodes) { case empty: case tree(n0, lns, rns): }
    {
        struct node *nodeRight = node->right;
        node->right = n;
        //@ close subtree(0, n, empty);
        //@ close subtree(0, n, empty);
        //@ close subtree(n, node, tree(n, empty, empty));
        //@ close context(n, node, 1, right_context(contextNodes, node, lns));
        fixup_ancestors(n, node, 1);
        //@ close tree(n, right_context(contextNodes, node, lns), tree(n, empty, empty));
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
    struct node *parent = node->parent;
    //@ switch(contextNodes) { case root: case left_context(pc, p0, rns): close tree(parent, pc, tree(parent, subtreeNodes, rns)); case right_context(pc, p0, lns): close tree(parent, pc, tree(parent, lns, subtreeNodes)); }
    return parent;
}


void dispose_node(struct node *node)
    //@ requires subtree(node, _, ?nodes);
    //@ ensures true;
{
    //@ open subtree(node, _, nodes);
    if (node == 0) {
    } else {
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
    //@ open context(node, 0, _, root);
    dispose_node(node);
}


// TODO: make this function pass the verification
int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *node0 = create_tree();
    struct node *node = node0;
    node = tree_add_left(node);
    node = tree_add_right(node);
    node = tree_get_parent(node);
    node = tree_add_left(node);
    node = tree_get_parent(node);
    node = tree_get_parent(node);
    tree_dispose(node);
    return 0;
}
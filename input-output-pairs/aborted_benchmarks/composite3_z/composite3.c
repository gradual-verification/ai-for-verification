#include "malloc.h"
#include <stdbool.h>

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

predicate subtree(struct node *root, struct node *parent, tree nodes) =
        switch (nodes) {
            case empty: return root == 0;
            case tree(root0, leftNodes, rightNodes):
                return
                    root == root0 &*& root != 0 &*&
                    root->left |-> ?left &*& root->right |-> ?right &*& root->parent |-> parent &*& root->count |-> tree_count(nodes) &*& malloc_block_node(root) &*&
                    subtree(left, root, leftNodes) &*& subtree(right, root, rightNodes);
        };

inductive context = root | left_context(context, struct node *, tree) | right_context(context, struct node *, tree);

predicate context(struct node *node, struct node *parent, int count, context nodes) = 
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

predicate tree(struct node *node, context contextNodes, tree subtreeNodes) = 
    context(node, ?parent, tree_count(subtreeNodes), contextNodes) &*& subtree(node, parent, subtreeNodes);

@*/

void abort();
    //@ requires true;
    //@ ensures false;

struct node *create_tree()
    //@ requires emp;
    //@ ensures tree(result, root, tree(result, empty, empty));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    //@ close subtree(0, n, empty);
    n->right = 0;
    //@ close subtree(0, n, empty);
    n->parent = 0;
    n->count = 1;
    //@ close subtree(n, 0, tree(n, empty, empty));
    //@ close context(n, 0, 1, root);
    //@ close tree(n, root, tree(n, empty, empty));
    return n;
}

int subtree_get_count(struct node *node)
    //TODO: need to fix the error below, the error is No matching heap chunks: subtree(node, _, _)VeriFast
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

int tree_get_count(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes);
    //@ ensures tree(node, contextNodes, subtreeNodes) &*& result == tree_count(subtreeNodes);
{
    //@ open tree(node, contextNodes, subtreeNodes);
    int result = subtree_get_count(node);
    //@ close tree(node, contextNodes, subtreeNodes);
    return result;
}

void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires context(node, parent, _, ?contextNodes);
    //@ ensures context(node, parent, count, contextNodes);
{
    //@ open context(node, parent, _, contextNodes);
    if (parent == 0) {
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left) {
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else {
            leftCount = subtree_get_count(left);
            rightCount = count;
        }
        {
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
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    //@ close subtree(0, n, empty);
    n->right = 0;
    //@ close subtree(0, n, empty);
    n->parent = node;
    n->count = 1;
    //@ close subtree(n, node, tree(n, empty, empty));
    //@ open subtree(node, ?parent, subtreeNodes);
    //@ struct node *nodeRight = node->right;
    //@ assert subtree(nodeRight, node, ?rightNodes);
    {
        struct node *nodeLeft = node->left;
        //@ open subtree(nodeLeft, node, empty);
        node->left = n;
        //@ close context(n, node, 0, left_context(contextNodes, node, rightNodes));
        fixup_ancestors(n, node, 1);
    }
    //@ close tree(n, left_context(contextNodes, node, rightNodes), tree(n, empty, empty));
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
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    //@ close subtree(0, n, empty);
    n->right = 0;
    //@ close subtree(0, n, empty);
    n->parent = node;
    n->count = 1;
    //@ close subtree(n, node, tree(n, empty, empty));
    //@ open subtree(node, ?parent, subtreeNodes);
    //@ struct node *nodeLeft = node->left;
    //@ assert subtree(nodeLeft, node, ?leftNodes);
    {
        struct node *nodeRight = node->right;
        //@ open subtree(nodeRight, node, empty);
        node->right = n;
        //@ close context(n, node, 0, right_context(contextNodes, node, leftNodes));
        fixup_ancestors(n, node, 1);
    }
    //@ close tree(n, right_context(contextNodes, node, leftNodes), tree(n, empty, empty));
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
    //@ open subtree(node, _, subtreeNodes);
    struct node *parent = node->parent;
    //@ close subtree(node, parent, subtreeNodes);
    //@ open context(node, parent, tree_count(subtreeNodes), contextNodes);
    //@ assert context(parent, ?grandparent, ?parentCount, ?parentContextNodes);
    /*@ switch (contextNodes) {
            case root:
            case left_context(parentContextNodes, parent0, rightNodes):
                close subtree(parent, grandparent, tree(parent, subtreeNodes, rightNodes));
            case right_context(parentContextNodes, parent0, leftNodes):
                close subtree(parent, grandparent, tree(parent, leftNodes, subtreeNodes));
        }
    @*/
    //@ assert subtree(parent, grandparent, ?parentNodes);
    //@ close tree(parent, parentContextNodes, parentNodes);
    return parent;
}

struct node *tree_get_left(struct node *node)
    /*@ requires tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return leftNodes != empty;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, left_context(contextNodes, node, rightNodes), leftNodes);
            };
    @*/
{
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?parent, subtreeNodes);
    struct node *left = node->left;
    //@ assert subtree(left, node, ?leftNodes);
    //@ struct node *right = node->right;
    //@ assert subtree(right, node, ?rightNodes);
    //@ close context(left, node, tree_count(leftNodes), left_context(contextNodes, node, rightNodes));
    //@ close tree(left, left_context(contextNodes, node, rightNodes), leftNodes);
    return left;
}

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
    //@ struct node *left = node->left;
    //@ assert subtree(left, node, ?leftNodes);
    struct node *right = node->right;
    //@ assert subtree(right, node, ?rightNodes);
    //@ close context(right, node, tree_count(rightNodes), right_context(contextNodes, node, leftNodes));
    //@ close tree(right, right_context(contextNodes, node, leftNodes), rightNodes);
    return right;
}

bool tree_has_parent(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes) &*& subtreeNodes != empty;
    //@ ensures tree(node, contextNodes, subtreeNodes) &*& result == (contextNodes != root);
{
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?parent, subtreeNodes);
    struct node *parent = node->parent;
    //@ close subtree(node, parent, subtreeNodes);
    //@ open context(node, parent, ?count, contextNodes);
    //@ close context(node, parent, count, contextNodes);
    //@ close tree(node, contextNodes, subtreeNodes);
    return parent != 0;
}

bool tree_has_left(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes) &*& subtreeNodes != empty;
    /*@ ensures
            tree(node, contextNodes, subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return result == (leftNodes != empty);
            };
    @*/
{
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?parent, subtreeNodes);
    struct node *left = node->left;
    //@ open subtree(left, node, ?leftNodes);
    //@ close subtree(left, node, leftNodes);
    //@ close subtree(node, parent, subtreeNodes);
    //@ close tree(node, contextNodes, subtreeNodes);
    return left != 0;
}

bool tree_has_right(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes) &*& subtreeNodes != empty;
    /*@ ensures
            tree(node, contextNodes, subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return result == (rightNodes != empty);
            };
    @*/
{
    //@ open tree(node, contextNodes, subtreeNodes);
    //@ open subtree(node, ?parent, subtreeNodes);
    struct node *right = node->right;
    //@ open subtree(right, node, ?rightNodes);
    //@ close subtree(right, node, rightNodes);
    //@ close subtree(node, parent, subtreeNodes);
    //@ close tree(node, contextNodes, subtreeNodes);
    return right != 0;
}

void dispose_node(struct node *node)
    //@ requires subtree(node, _, _);
    //@ ensures emp;
{
    //@ open subtree(node, _, _);
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
    //@ requires tree(node, root, _);
    //@ ensures emp;
{
    //@ open tree(node, root, _);
    //@ open context(node, _, _, root);
    dispose_node(node);
}

int main()
    //@ requires emp;
    //@ ensures emp;
{
    struct node *node0 = create_tree();
    struct node *node = node0;
    node = tree_add_left(node);
    node = tree_add_right(node);
    node = tree_get_parent(node);
    node = tree_add_left(node);
    node = tree_get_parent(node);
    node = tree_get_parent(node);
    //@ assert(node == node0);
    tree_dispose(node);
    return 0;
}

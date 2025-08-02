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



struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close subtree(0, n, 0);
    //@ close subtree(0, n, 0);
    //@ close subtree(n, 0, 1);
    //@ close context(n, 0, 1);
    //@ close tree(n);
    return n;
}


int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?parent, ?count);
    //@ ensures subtree(node, parent, count) &*& result == count;
{
    int result = 0;
    if (node == 0) {
        //@ open subtree(node, parent, count);
        //@ close subtree(node, parent, count);
    } else {
        //@ open subtree(node, parent, count);
        result = node->count;
        //@ close subtree(node, parent, count);
    }
    return result;
}


int tree_get_count(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(node);
{
    //@ open tree(node);
    //@ open context(node, ?parent, ?count);
    int result = subtree_get_count(node);
    //@ close context(node, parent, count);
    //@ close tree(node);
    return result;
}


void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires context(node, parent, ?oldCount);
    //@ ensures context(node, parent, count);
{
    if (parent == 0) {
        //@ open context(node, parent, oldCount);
        //@ close context(node, parent, count);
    } else {
        //@ open context(node, parent, oldCount);
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
        // to avoid integer overflow
        if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        fixup_ancestors(parent, grandparent, parentCount);
        //@ close context(node, parent, count);
    }
}


struct node *tree_add_left(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    if (node == 0) {
        abort();
    }
    {
        //@ open tree(node);
        //@ open context(node, ?parent, ?count);
        //@ open subtree(node, parent, count);
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
            if (nodeLeft != 0) {
                abort();
            }
            node->left = n;
            if (n == node->right) {
                abort();
            }
            //@ close subtree(0, n, 0);
            //@ close subtree(0, n, 0);
            //@ close subtree(n, node, 1);
            //@ close context(n, node, 1);
            fixup_ancestors(n, node, 1);
            //@ close tree(n);
        }
        return n;
    }
}


struct node *tree_add_right(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    if (node == 0) {
        abort();
    }
    {
        //@ open tree(node);
        //@ open context(node, ?parent, ?count);
        //@ open subtree(node, parent, count);
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
            if (nodeRight != 0) {
                abort();
            }
            node->right = n;
            if (n == node->left) {
                abort();
            }
            //@ close subtree(0, n, 0);
            //@ close subtree(0, n, 0);
            //@ close subtree(n, node, 1);
            //@ close context(n, node, 1);
            fixup_ancestors(n, node, 1);
            //@ close tree(n);
        }
        return n;
    }
}


struct node *tree_get_parent(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    if (node == 0) {
        abort();
    }
    {
        //@ open tree(node);
        //@ open context(node, ?parent, ?count);
        //@ open subtree(node, parent, count);
        struct node *parent = node->parent;
        if (parent == 0) {
            abort();
        }
        //@ close subtree(node, parent, count);
        //@ close tree(parent);
        return parent;
    }
}


void dispose_node(struct node *node)
    //@ requires subtree(node, _, _);
    //@ ensures true;
{
    if (node == 0) {
        //@ open subtree(node, _, _);
    } else {
        //@ open subtree(node, _, _);
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
    //@ requires tree(node);
    //@ ensures true;
{
    if (node == 0) {
        abort();
    }
    {
        //@ open tree(node);
        //@ open context(node, ?parent, ?count);
        struct node *parent = node->parent;
        if (parent != 0) {
            abort();
        }
        //@ close context(node, parent, count);
        //@ open context(node, parent, count);
        dispose_node(node);
    }
}


int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *node = create_tree();
    node = tree_add_left(node);
    node = tree_add_right(node);
    node = tree_get_parent(node);
    node = tree_add_left(node);
    node = tree_get_parent(node);
    node = tree_get_parent(node);
    tree_dispose(node);
    return 0;
}
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
            malloc_block_node(root) &*&
            subtree(left, root, ?leftCount) &*& subtree(right, root, ?rightCount) &*& count == 1 + leftCount + rightCount;

predicate context(struct node *node, struct node *parent, int count) = 
        parent == 0 ?
            true
        :
            parent->left |-> ?left &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*&
            malloc_block_node(parent) &*&
            context(parent, grandparent, parentCount) &*&
            (node == left ? 
                 subtree(right, parent, ?rightCount) &*& parentCount == 1 + count + rightCount
             :
                 node == right &*& subtree(left, parent, ?leftCount) &*& parentCount == 1 + count + leftCount
            );

predicate tree(struct node *node) = 
    context(node, ?parent, ?count) &*& subtree(node, parent, count);
@*/



int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?parent, ?count);
    //@ ensures subtree(node, parent, count) &*& result == count;
{
    int result = 0;
    //@ open subtree(node, parent, count);
    if (node == 0) {
        //@ assert count == 0;
    } else {
        result = node->count;
        //@ assert result == count;
    }
    //@ close subtree(node, parent, count);
    return result;
}


void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires context(node, parent, ?oldCount);
    //@ ensures context(node, parent, count);
{
    //@ open context(node, parent, oldCount);
    if (parent == 0) {
    } else {
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
    }
    //@ close context(node, parent, count);
}


// TODO: make this function pass the verification
struct node *tree_add_left(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    if (node == 0) {
        abort();
    }
    //@ open tree(node);
    {
        struct node *n = malloc(sizeof(struct node));
        if (n == 0) {
            abort();
        }
        n->left = 0;
        n->right = 0;
        n->parent = node;
        n->count = 1;
        //@ close subtree(0, n, 0);
        //@ close subtree(0, n, 0);
        //@ close subtree(n, node, 1);
        {
            //@ open subtree(node, ?p, ?c);
            struct node *nodeLeft = node->left;
            if (nodeLeft != 0) {
                abort();
            }
            //@ open subtree(nodeLeft, node, ?leftCount);
            //@ assert leftCount == 0;
            
            node->left = n;
            if (n == node->right) {
                abort();
            }
            //@ close context(n, node, 0);
            fixup_ancestors(n, node, 1);
            //@ close tree(n);
        }
        return n;
    }
}
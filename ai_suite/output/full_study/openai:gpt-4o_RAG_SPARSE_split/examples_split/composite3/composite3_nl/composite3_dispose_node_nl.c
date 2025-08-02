#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate tree(struct node *n) =
    n == 0 ? true :
    n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &*& n->count |-> _ &*&
    malloc_block_node(n) &*&
    tree(left) &*& tree(right);

@*/

// TODO: make this function pass the verification
void dispose_node(struct node *node)
    //@ requires tree(node);
    //@ ensures true;
{
    if (node == 0) {
        //@ close tree(0);
    } else {
        {
            struct node *left = node->left;
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        //@ open tree(node);
        free(node);
    }
}
#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate node(struct node *n;) =
    n == 0 ? emp : 
    n->left |-> ?left &*& n->right |-> ?right &*& n->parent |-> ?parent &*& n->count |-> _ &*&
    malloc_block_node(n) &*& node(left) &*& node(right);

@*/

// TODO: make this function pass the verification
void dispose_node(struct node *node)
    //@ requires node(node);
    //@ ensures emp;
{
    if (node == 0) {
        //@ open node(node);
    } else {
        {
            struct node *left = node->left;
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        //@ open node(node);
        free(node);
    }
}
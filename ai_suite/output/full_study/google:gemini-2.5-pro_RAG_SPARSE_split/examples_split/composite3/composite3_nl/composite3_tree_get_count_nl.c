#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
predicate subtree(struct node *n, struct node *p; int count) =
    n == 0 ?
        count == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> count &*&
        malloc_block_node(n) &*&
        subtree(l, n, ?lc) &*&
        subtree(r, n, ?rc) &*&
        count == 1 + lc + rc;

predicate tree(struct node *n; int count) =
    subtree(n, 0, count);
@*/


/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?p, ?c);
    //@ ensures subtree(node, p, c) &*& result == c;
{
    int result = 0;
    if (node == 0) {
        //@ open subtree(node, p, c);
        //@ close subtree(node, p, c);
    } else {
        //@ open subtree(node, p, c);
        result = node->count;
        //@ close subtree(node, p, c);
    }
    return result;
}


// TODO: make this function pass the verification
/*tree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the tree is unchanged and the returned value is the count of the tree.
*/
int tree_get_count(struct node *node)
    //@ requires tree(node, ?c);
    //@ ensures tree(node, c) &*& result == c;
{
    //@ open tree(node, c);
    int result = subtree_get_count(node);
    //@ close tree(node, c);
    return result;
}
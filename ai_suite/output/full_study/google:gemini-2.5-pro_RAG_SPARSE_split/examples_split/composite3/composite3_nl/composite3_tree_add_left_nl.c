#include "stdlib.h"
#include "limits.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate subtree(struct node *n, struct node *p, int count) =
    n == 0 ?
        count == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> count &*&
        malloc_block(n, sizeof(struct node)) &*&
        subtree(l, n, ?lc) &*&
        subtree(r, n, ?rc) &*&
        count == 1 + lc + rc;

predicate tree_path(struct node *child, struct node *parent) =
    parent == 0 ?
        child->parent |-> 0
    :
        child->parent |-> parent &*&
        parent->left |-> ?l &*&
        parent->right |-> ?r &*&
        parent->parent |-> ?gp &*&
        parent->count |-> _ &*&
        malloc_block(parent, sizeof(struct node)) &*&
        (child == l ?
            subtree(r, parent, _)
        :
            subtree(l, parent, _)
        ) &*&
        tree_path(parent, gp);

predicate tree_path_with_counts(struct node *child, struct node *parent) =
    parent == 0 ?
        child->parent |-> 0
    :
        child->parent |-> parent &*&
        subtree(parent, ?gp, _) &*&
        tree_path_with_counts(parent, gp);

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
    //@ open subtree(node, p, c);
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    //@ close subtree(node, p, c);
    return result;
}


/*fixup_ancestors function
-param: struct node *node, struct node *parent, int count
-description: The function fixes the count of the ancestors
of the current node. Here, parameter `count` is the number of nodes
in the subtree rooted at node.

It makes sure that the counts of the node and ancestors are updated correctly.
*/
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires subtree(node, parent, count) &*& tree_path(node, parent);
    //@ ensures tree_path_with_counts(node, parent);
{
    //@ open tree_path(node, parent);
    if (parent == 0) {
        //@ close tree_path_with_counts(node, 0);
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            leftCount = count;
            //@ assert subtree(right, parent, ?rc);
            rightCount = subtree_get_count(right);
            //@ assert rc == rightCount;
            //@ close subtree(node, parent, count);
        } else if (node == right && node != left) {
            //@ assert subtree(left, parent, ?lc);
            leftCount = subtree_get_count(left);
            //@ assert lc == leftCount;
            rightCount = count;
            //@ close subtree(node, parent, count);
        } else {
            abort();
        }
        {
            if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            //@ close subtree(parent, grandparent, parentCount);
            fixup_ancestors(parent, grandparent, parentCount);
            //@ close tree_path_with_counts(node, parent);
        }
    }
}


// TODO: make this function pass the verification
/*tree_add_left function
-param: struct node *node
-description: The function adds a left node to the
current node. It requires that before the call, the current node is non-null and its left node is null.
It returns the newly added node and makes sure that it is the left child of the given node.
*/
struct node *tree_add_left(struct node *node)
    /*@ requires node != 0 &*&
                 node->left |-> 0 &*&
                 node->right |-> ?r &*&
                 node->parent |-> ?p &*&
                 node->count |-> ?c &*&
                 malloc_block(node, sizeof(struct node)) &*&
                 subtree(r, node, ?rc) &*&
                 c == 1 + rc &*&
                 tree_path(node, p);
    @*/
    /*@ ensures subtree(result, node, 1) &*&
                tree_path_with_counts(result, node);
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
    //@ close subtree(0, n, 0);
    //@ close subtree(0, n, 0);
    //@ close subtree(n, node, 1);
    {
        struct node *nodeLeft = node->left;
        node->left = n;
        //@ close tree_path(n, node);
        fixup_ancestors(n, node, 1);
    }
    return n;
}
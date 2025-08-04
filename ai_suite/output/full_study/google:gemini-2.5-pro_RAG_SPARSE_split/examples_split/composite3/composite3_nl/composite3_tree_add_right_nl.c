#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate tree(struct node *n, struct node *p, int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> c &*&
        malloc_block_node(n) &*&
        tree(l, n, ?lc) &*& tree(r, n, ?rc) &*&
        c == 1 + lc + rc &*& 0 <= lc &*& 0 <= rc;

predicate node_fields(struct node *n; struct node *l, struct node *r, struct node *p, int c) =
    n->left |-> l &*& n->right |-> r &*& n->parent |-> p &*& n->count |-> c &*& malloc_block_node(n);

predicate ancestor_path_shape(struct node *child, struct node *p) =
    p == 0 ?
        true
    :
        node_fields(p, ?l, ?r, ?gp, _) &*&
        (child == l ? tree(r, p, _) : tree(l, p, _)) &*&
        ancestor_path_shape(p, gp);

predicate ancestor_path(struct node *child, struct node *p, int child_count) =
    p == 0 ?
        true
    :
        p->left |-> ?l &*& p->right |-> ?r &*& p->parent |-> ?gp &*&
        malloc_block_node(p) &*&
        (child == l ?
            tree(r, p, ?rc) &*& p->count |-> (1 + child_count + rc) &*& ancestor_path(p, gp, 1 + child_count + rc)
        :
            tree(l, p, ?lc) &*& p->count |-> (1 + lc + child_count) &*& ancestor_path(p, gp, 1 + lc + child_count)
        );

lemma void ancestor_path_to_shape(struct node *child, struct node *p)
    requires ancestor_path(child, p, ?c);
    ensures ancestor_path_shape(child, p);
{
    open ancestor_path(child, p, c);
    if (p != 0) {
        ancestor_path_to_shape(p, p->parent);
        close node_fields(p, p->left, p->right, p->parent, p->count);
    }
    close ancestor_path_shape(child, p);
}

@*/


/*subtree_get_count function
-param: struct node *node
-description: The function gets the count of the current node,
which is the number of nodes in the subtree rooted at the node.

It makes sure that the subtree is unchanged and the returned value is the count of the subtree.
*/
int subtree_get_count(struct node *node)
    //@ requires tree(node, ?p, ?c);
    //@ ensures tree(node, p, c) &*& result == c;
{
    //@ open tree(node, p, c);
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    //@ close tree(node, p, c);
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
    //@ requires tree(node, parent, count) &*& ancestor_path_shape(node, parent);
    //@ ensures tree(node, parent, count) &*& ancestor_path(node, parent, count);
{
    //@ open ancestor_path_shape(node, parent);
    if (parent == 0) {
        //@ close ancestor_path(node, 0, count);
    } else {
        //@ open node_fields(parent, ?left, ?right, ?grandparent, _);
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

            if (node == left) {
                //@ close tree(parent, grandparent, parentCount);
            } else {
                //@ close tree(parent, grandparent, parentCount);
            }

            fixup_ancestors(parent, grandparent, parentCount);

            //@ open tree(parent, grandparent, parentCount);
            //@ if (node == left) {
            //@     close ancestor_path(node, parent, count);
            //@ } else {
            //@     close ancestor_path(node, parent, count);
            //@ }
        }
    }
}


/*tree_add_right function
-param: struct node *node
-description: The function adds a right node to the
current node. It requires that before the call, the current node is non-null and its right node is null.
It returns the newly added node and makes sure that it is the right child of the given node.
*/
struct node *tree_add_right(struct node *node)
    //@ requires node != 0 &*& node_fields(node, ?l, 0, ?p, ?c) &*& tree(l, node, ?lc) &*& c == 1 + lc &*& ancestor_path(node, p, c);
    //@ ensures tree(result, node, 1) &*& ancestor_path(result, node, 1) &*& result != 0;
{
    //@ open node_fields(node, l, 0, p, c);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    //@ close tree(0, n, 0);
    //@ close tree(0, n, 0);
    //@ close tree(n, node, 1);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        
        ancestor_path_to_shape(node, p);
        //@ close node_fields(node, l, n, p, c);
        //@ close ancestor_path_shape(n, node);
        
        fixup_ancestors(n, node, 1);
    }
    return n;
}
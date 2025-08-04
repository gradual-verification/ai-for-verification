#include "stdlib.h"
#include "limits.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
predicate node(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    malloc_block_node(n);

predicate tree(struct node *n, struct node *p, int c) =
    n == 0 ?
        c == 0
    :
        c > 0 &*&
        node(n, ?l, ?r, p, c) &*&
        tree(l, n, ?lc) &*&
        tree(r, n, ?rc) &*&
        c == 1 + lc + rc;

predicate parent_path(struct node *child, struct node *p) =
    p == 0 ?
        true
    :
        node(p, ?l, ?r, ?gp, _) &*&
        (
            l == child && r != child ?
                tree(r, p, ?rc) &*& parent_path(p, gp)
            :
            r == child && l != child ?
                tree(l, p, ?lc) &*& parent_path(p, gp)
            :
                false
        );

predicate parent_path_fixed(struct node *child, struct node *p, int child_count) =
    p == 0 ?
        true
    :
        node(p, ?l, ?r, ?gp, ?p_c) &*&
        (
            l == child && r != child ?
                tree(r, p, ?rc) &*& p_c == 1 + child_count + rc &*& parent_path_fixed(p, gp, p_c)
            :
            r == child && l != child ?
                tree(l, p, ?lc) &*& p_c == 1 + lc + child_count &*& parent_path_fixed(p, gp, p_c)
            :
                false
        );

lemma void parent_path_fixed_to_parent_path_lemma(struct node *child, struct node *p)
    requires parent_path_fixed(child, p, ?c);
    ensures parent_path(child, p);
{
    open parent_path_fixed(child, p, c);
    if (p != 0) {
        parent_path_fixed_to_parent_path_lemma(p, p->parent);
        close parent_path(child, p);
    } else {
        close parent_path(child, p);
    }
}
@*/

/*create_tree function
-param: void
-description: The function creates a tree with one node and returns it.

It makes sure that the returned value is a tree with one node.
*/
struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, 0, 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = 0;
    n->count = 1;
    //@ close tree(0, n, 0);
    //@ close tree(0, n, 0);
    //@ close tree(n, 0, 1);
    return n;
}


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
    int result = 0;
    //@ open tree(node, p, c);
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
    //@ requires tree(node, parent, count) &*& parent_path(node, parent);
    //@ ensures parent_path_fixed(node, parent, count) &*& tree(node, parent, count);
{
    //@ open parent_path(node, parent);
    if (parent == 0) {
        //@ close parent_path_fixed(node, 0, count);
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
        {
            if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            
            //@ if (node == left && node != right) { close tree(parent, grandparent, parentCount); }
            //@ else { close tree(parent, grandparent, parentCount); }

            fixup_ancestors(parent, grandparent, parentCount);
            
            //@ open tree(parent, grandparent, parentCount);
            //@ close parent_path_fixed(node, parent, count);
        }
    }
}


/*tree_add_left function
-param: struct node *node
-description: The function adds a left node to the
current node. It requires that before the call, the current node is non-null and its left node is null.
It returns the newly added node and makes sure that it is the left child of the given node.
*/
struct node *tree_add_left(struct node *node)
    //@ requires tree(node, ?gp, ?pc) &*& node->left == 0 &*& parent_path(node, gp);
    //@ ensures tree(node, gp, pc + 1) &*& parent_path(node, gp) &*& result == node->left;
{
    //@ open tree(node, gp, pc);
    //@ assert node(node, 0, ?r, gp, pc) &*& tree(0, node, 0) &*& tree(r, node, ?rc) &*& pc == 1 + rc;
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    //@ close tree(n, node, 1);
    {
        struct node *nodeLeft = node->left;
        node->left = n;
        //@ close parent_path(n, node);
        fixup_ancestors(n, node, 1);
        //@ assert parent_path_fixed(n, node, 1) &*& tree(n, node, 1);
        //@ open parent_path_fixed(n, node, 1);
        //@ assert node(node, n, r, gp, 1 + 1 + rc) &*& tree(r, node, rc) &*& parent_path_fixed(node, gp, 1 + 1 + rc);
        //@ close tree(node, gp, pc + 1);
        parent_path_fixed_to_parent_path_lemma(node, gp);
    }
    return n;
}


/*tree_add_right function
-param: struct node *node
-description: The function adds a right node to the
current node. It requires that before the call, the current node is non-null and its right node is null.
It returns the newly added node and makes sure that it is the right child of the given node.
*/
struct node *tree_add_right(struct node *node)
    //@ requires tree(node, ?gp, ?pc) &*& node->right == 0 &*& parent_path(node, gp);
    //@ ensures tree(node, gp, pc + 1) &*& parent_path(node, gp) &*& result == node->right;
{
    //@ open tree(node, gp, pc);
    //@ assert node(node, ?l, 0, gp, pc) &*& tree(l, node, ?lc) &*& tree(0, node, 0) &*& pc == 1 + lc;
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = node;
    n->count = 1;
    //@ close tree(n, node, 1);
    {
        struct node *nodeRight = node->right;
        node->right = n;
        //@ close parent_path(n, node);
        fixup_ancestors(n, node, 1);
        //@ assert parent_path_fixed(n, node, 1) &*& tree(n, node, 1);
        //@ open parent_path_fixed(n, node, 1);
        //@ assert node(node, l, n, gp, 1 + lc + 1) &*& tree(l, node, lc) &*& parent_path_fixed(node, gp, 1 + lc + 1);
        //@ close tree(node, gp, pc + 1);
        parent_path_fixed_to_parent_path_lemma(node, gp);
    }
    return n;
}


/*tree_get_parent function
-param: struct node *node
-description: The function gets the parent of the
current node. It requires that before the call, the current node and its parent are non-null.
It makes sure that the returned value is the parent of the current node and the tree is not changed.
*/
struct node *tree_get_parent(struct node *node)
    //@ requires tree(node, ?p, ?c);
    //@ ensures tree(node, p, c) &*& result == p;
{
    //@ open tree(node, p, c);
    struct node *parent = node->parent;
    //@ close tree(node, p, c);
    return parent;
}


/*dispose_node function
-param: struct node *node
-description: The function disposes the tree by calling
itself recursively on the left and right nodes of the
current node. It then frees the current node.

It makes sure that the subtree of node is freed.
*/
void dispose_node(struct node *node)
    //@ requires tree(node, ?p, ?c);
    //@ ensures true;
{
    //@ open tree(node, p, c);
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


/*tree_dispose function
-param: struct node *node
-description: The function disposes the tree by calling 
the dispose_node function.

It makes sure that the tree of noed is freed.
*/
void tree_dispose(struct node *node)
    //@ requires tree(node, 0, ?c);
    //@ ensures true;
{
    dispose_node(node);
}


// TODO: make this function pass the verification
/*main function
-param: void
-description: The function creates a tree and adds 
left and right nodes to the tree. It then gets the 
parent of the right node and adds a left node to it.
It then gets the parent of the left node and disposes 
the tree.
*/
int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *node0 = create_tree();
    struct node *node = node0;
    
    //@ close parent_path(node0, 0);
    node = tree_add_left(node);
    //@ struct node *node1 = node;
    
    //@ open tree(node0, 0, 2);
    //@ assert node(node0, node1, 0, 0, 2) &*& tree(node1, node0, 1) &*& tree(0, node0, 0);
    //@ close parent_path(node1, node0);
    node = tree_add_right(node);
    //@ struct node *node2 = node;
    
    node = tree_get_parent(node);
    //@ assert node == node1;
    
    //@ open tree(node1, node0, 2);
    //@ assert node(node1, 0, node2, node0, 2) &*& tree(0, node1, 0) &*& tree(node2, node1, 1);
    //@ close parent_path(node1, node0);
    node = tree_add_left(node);
    //@ struct node *node3 = node;
    
    node = tree_get_parent(node);
    //@ assert node == node1;
    
    node = tree_get_parent(node);
    //@ assert node == node0;
    
    //@ open tree(node1, node0, 3);
    //@ assert node(node1, node3, node2, node0, 3) &*& tree(node3, node1, 1) &*& tree(node2, node1, 1);
    //@ close tree(node0, 0, 4);
    tree_dispose(node);
    return 0;
}
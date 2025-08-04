#include "stdlib.h"
#include "limits.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

// A predicate for the fields of a single node.
predicate node_fields(struct node *n; struct node *left, struct node *right, struct node *parent, int count) =
    n != 0 &*&
    n->left |-> left &*&
    n->right |-> right &*&
    n->parent |-> parent &*&
    n->count |-> count &*&
    malloc_block_node(n);

// A predicate for a well-formed tree (or subtree).
// It recursively checks the tree structure, parent pointers, and counts.
// 'p' is the expected parent of the root 'n'.
// 'c' is the number of nodes in the tree rooted at 'n'.
predicate tree(struct node *n, struct node *p; int c) =
    n == 0 ?
        c == 0
    :
        node_fields(n, ?l, ?r, p, c) &*&
        tree(l, n, ?lc) &*&
        tree(r, n, ?rc) &*&
        c == 1 + lc + rc;

// A predicate for the "context" of a node 'n' up to an ancestor 'p'.
// It owns the ancestor chain from 'n' to the root of the whole tree.
// It also owns the sibling subtrees along this path.
// 'root' is an output parameter that will be the root of the entire tree.
predicate ancestor_chain(struct node *n, struct node *p; struct node *root) =
    p == 0 ?
        root == n
    :
        node_fields(p, ?l, ?r, ?gp, _) &*&
        (l == n && r != n ? tree(r, p, _) :
         r == n && l != n ? tree(l, p, _) :
         false) &*&
        ancestor_chain(p, gp, root);

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


// TODO: make this function pass the verification
/*fixup_ancestors function
-param: struct node *node, struct node *parent, int count
-description: The function fixes the count of the ancestors
of the current node. Here, parameter `count` is the number of nodes
in the subtree rooted at node.

It makes sure that the counts of the node and ancestors are updated correctly.
*/
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires tree(node, parent, count) &*& ancestor_chain(node, parent, ?root);
    //@ ensures tree(root, 0, _);
{
    //@ open ancestor_chain(node, parent, root);
    if (parent == 0) {
        //@ assert root == node;
    } else {
        //@ assert node_fields(parent, ?l, ?r, ?gp, _);
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
            
            //@ close tree(parent, grandparent, parentCount);
            
            fixup_ancestors(parent, grandparent, parentCount);
        }
    }
}
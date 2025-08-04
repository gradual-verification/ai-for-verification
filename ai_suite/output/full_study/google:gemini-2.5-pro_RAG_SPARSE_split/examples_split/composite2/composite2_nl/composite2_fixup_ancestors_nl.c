#include "stdlib.h"
#include "limits.h"
#include "malloc.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate is_tree(struct node *n, struct node *p; int count) =
    n == 0 ?
        count == 0
    :
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> count &*&
        malloc_block_node(n) &*&
        is_tree(l, n, ?left_count) &*&
        is_tree(r, n, ?right_count) &*&
        count == 1 + left_count + right_count &*&
        0 <= left_count &*& 0 <= right_count;

predicate ancestors(struct node *child, struct node *p; struct node *root, struct node *root_parent) =
    p == 0 ?
        child == root &*& p == root_parent
    :
        p->left |-> ?l &*& p->right |-> ?r &*& p->parent |-> ?gp &*& p->count |-> _ &*&
        malloc_block_node(p) &*&
        (child == l ?
            is_tree(r, p, _)
        : child == r ?
            is_tree(l, p, _)
        :
            false
        ) &*&
        ancestors(p, gp, root, root_parent);

@*/


/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires is_tree(node, ?p, ?c);
    //@ ensures is_tree(node, p, c) &*& result == c;
{
    //@ open is_tree(node, p, c);
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    //@ close is_tree(node, p, c);
    return result;
}


// TODO: make this function pass the verification
/*`fixup_ancestors()` Function:
- Parameters: Takes a node pointer, parent pointer, 
and the new count as input.
- Description: This function updates the count of the
  ancestors of the provided node based on the new count
  provided.
  
It makes sure that the node's count is updated with the given value and the ancestors' count is also updated. */
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires is_tree(node, parent, count) &*& ancestors(node, parent, ?root, ?root_parent);
    //@ ensures is_tree(root, root_parent, _);
{
    //@ open ancestors(node, parent, root, root_parent);
    if (parent == 0) {
        //@ assert node == root && parent == root_parent;
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            leftCount = count;
            rightCount = subtree_get_count(right);
            //@ assert is_tree(right, parent, rightCount);
        } else if (node == right && node != left) {
            leftCount = subtree_get_count(left);
            //@ assert is_tree(left, parent, leftCount);
            rightCount = count;
        } else {
            abort();
        }
        // to avoid integer overflow
        //@ assert is_tree(node, parent, count) &*& count >= 0;
        //@ if (node == left) { assert rightCount >= 0; } else { assert leftCount >= 0; }
        if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort();}
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        
        //@ close is_tree(parent, grandparent, parentCount);
        fixup_ancestors(parent, grandparent, parentCount);
    }
}
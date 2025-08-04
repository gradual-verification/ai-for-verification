#include "stdlib.h"
#include "limits.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// A precise predicate representing a valid subtree.
// 'n' is the root of the subtree, 'p' is its parent.
// 'c' is the number of nodes in the subtree, which is guaranteed to be correct.
predicate subtree(struct node *n, struct node *p; int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> c &*&
        malloc_block_node(n) &*&
        subtree(l, n, ?lc) &*&
        subtree(r, n, ?rc) &*&
        c == 1 + lc + rc;

// A predicate representing the path from a node's parent to the tree's root.
// It owns the nodes on the path and all sibling subtrees.
// 'p' is the parent of 'child', 'root' is the root of the whole tree.
predicate ancestors(struct node *p, struct node *child; struct node *root) =
    p == 0 ?
        root == child &*& emp
    :
        p->left |-> ?l &*& p->right |-> ?r &*& p->parent |-> ?gp &*& p->count |-> _ &*&
        malloc_block_node(p) &*&
        (child == l ? subtree(r, p, _) : subtree(l, p, _)) &*&
        ancestors(gp, p, root);
@*/


/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires [?f]subtree(node, ?p, ?c);
    //@ ensures [f]subtree(node, p, c) &*& result == c;
{
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    return result;
}


/*`fixup_ancestors()` Function:
- Parameters: Takes a node pointer, parent pointer, 
and the new count as input.
- Description: This function updates the count of the
  ancestors of the provided node based on the new count
  provided.
  
It makes sure that the node's count is updated with the given value and the ancestors' count is also updated. */
void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires ancestors(parent, node, ?root) &*& subtree(node, parent, count);
    //@ ensures subtree(root, 0, _);
{
    //@ open ancestors(parent, node, root);
    if (parent == 0) {
        //@ assert root == node;
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            leftCount = count;
            //@ open subtree(right, parent, ?rc);
            rightCount = subtree_get_count(right);
            //@ assert rightCount == rc;
            //@ close subtree(right, parent, rc);
        } else if (node == right && node != left) {
            //@ open subtree(left, parent, ?lc);
            leftCount = subtree_get_count(left);
            //@ assert leftCount == lc;
            //@ close subtree(left, parent, lc);
            rightCount = count;
        } else {
            abort();
        }
        // to avoid integer overflow
        if (rightCount < 0 || leftCount > INT_MAX - 1 -rightCount) { abort();}
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        
        //@ close subtree(parent, grandparent, parentCount);
        fixup_ancestors(parent, grandparent, parentCount);
    }
}


// TODO: make this function pass the verification
/*`tree_add_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: It adds a new node as the right child 
of the input node by following a similar process 
of memory allocation, setting pointers, and 
updating count values. 

It makes sure to return the new node in the tree. */
struct node *tree_add_right(struct node *node)
    /*@ requires
            node != 0 &*&
            node->left |-> ?l &*& node->right |-> 0 &*& node->parent |-> ?p &*& node->count |-> ?c &*&
            malloc_block_node(node) &*&
            subtree(l, node, ?lc) &*& c == 1 + lc &*&
            ancestors(p, node, ?root);
    @*/
    //@ ensures subtree(root, 0, _) &*& result != 0;
{
    if (node == 0) {
        abort();
    }
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
            struct node *nodeRight = node->right;
            if (nodeRight != 0) {
                abort();
            }
            node->right = n;
            if (n == node->left) {
                abort();
            }
            
            // We have the necessary components to construct ancestors(node, n, root)
            // for the call to fixup_ancestors.
            //@ close ancestors(node, n, root);
            
            fixup_ancestors(n, node, 1);
        }
        return n;
    }
}
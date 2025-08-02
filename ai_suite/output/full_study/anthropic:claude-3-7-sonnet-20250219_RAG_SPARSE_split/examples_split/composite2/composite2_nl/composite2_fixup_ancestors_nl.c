#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Predicate to represent a valid subtree
predicate subtree(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->parent |-> ?parent &*&
        node->count |-> count &*&
        malloc_block_node(node) &*&
        subtree(left, ?leftCount) &*&
        subtree(right, ?rightCount) &*&
        count == 1 + leftCount + rightCount;
@*/

/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?count);
    //@ ensures subtree(node, count) &*& result == count;
{
    int result = 0;
    if (node == 0) {
        //@ open subtree(node, count);
        //@ close subtree(node, count);
    } else {
        //@ open subtree(node, count);
        result = node->count;
        //@ close subtree(node, count);
    }
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
    /*@ requires node != 0 &*& 
                 node->left |-> ?left &*& 
                 node->right |-> ?right &*& 
                 node->parent |-> parent &*& 
                 node->count |-> _ &*& 
                 malloc_block_node(node) &*&
                 subtree(left, ?leftCount) &*& 
                 subtree(right, ?rightCount) &*&
                 (parent == 0 ? true : 
                    parent->left |-> ?pleft &*& 
                    parent->right |-> ?pright &*& 
                    parent->parent |-> ?gparent &*& 
                    parent->count |-> ?pcount &*& 
                    malloc_block_node(parent) &*&
                    ((pleft == node && pright != node) || (pleft != node && pright == node)) &*&
                    (pleft == node ? 
                        subtree(pright, ?prightCount) : 
                        subtree(pleft, ?pleftCount)));
    @*/
    /*@ ensures node != 0 &*& 
                node->left |-> left &*& 
                node->right |-> right &*& 
                node->parent |-> parent &*& 
                node->count |-> count &*& 
                malloc_block_node(node) &*&
                subtree(left, leftCount) &*& 
                subtree(right, rightCount) &*&
                (parent == 0 ? true : 
                    parent->left |-> pleft &*& 
                    parent->right |-> pright &*& 
                    parent->parent |-> gparent &*& 
                    parent->count |-> ?newPcount &*& 
                    malloc_block_node(parent) &*&
                    (pleft == node ? 
                        subtree(pright, prightCount) &*& newPcount == 1 + count + prightCount : 
                        subtree(pleft, pleftCount) &*& newPcount == 1 + pleftCount + count));
    @*/
{
    if (parent == 0) {
        //@ close subtree(node, count);
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
        //@ close subtree(node, count);
        fixup_ancestors(parent, grandparent, parentCount);
    }
}
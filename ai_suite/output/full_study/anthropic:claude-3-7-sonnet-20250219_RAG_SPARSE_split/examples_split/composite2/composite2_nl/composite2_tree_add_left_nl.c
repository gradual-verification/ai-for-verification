#include "stdlib.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// Define a predicate for a node in the tree
predicate node_with_count(struct node *n; int c) =
    n != 0 &*&
    n->left |-> ?l &*&
    n->right |-> ?r &*&
    n->parent |-> ?p &*&
    n->count |-> c &*&
    malloc_block_node(n) &*&
    c == (l == 0 ? 0 : subtree_get_count(l)) + (r == 0 ? 0 : subtree_get_count(r)) + 1;

// Define a predicate for a subtree
predicate subtree(struct node *n; int count) =
    n == 0 ?
        count == 0
    :
        node_with_count(n, count) &*&
        subtree(n->left, ?lcount) &*&
        subtree(n->right, ?rcount) &*&
        count == lcount + rcount + 1;
@*/

/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node. 

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
//@ requires node == 0 ? true : [?f]node_with_count(node, ?count);
//@ ensures node == 0 ? result == 0 : [f]node_with_count(node, count) &*& result == count;
{
    int result = 0;
    if (node == 0) {
    } else {
        //@ open [f]node_with_count(node, count);
        result = node->count;
        //@ close [f]node_with_count(node, count);
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
//@ requires node != 0 &*& parent == 0 ? true : node_with_count(parent, _);
//@ ensures parent == 0 ? true : node_with_count(parent, _);
{
    if (parent == 0) {
    } else {
        //@ open node_with_count(parent, _);
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
        //@ close node_with_count(parent, parentCount);
        fixup_ancestors(parent, grandparent, parentCount);
    }
}


// TODO: make this function pass the verification
/*`tree_add_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function adds a new node
 as the left child of the input node.
 
It makes sure to return the new node in the tree.*/
struct node *tree_add_left(struct node *node)
//@ requires node != 0 &*& node_with_count(node, ?count) &*& node->left |-> 0;
//@ ensures node_with_count(node, ?new_count) &*& result != 0 &*& node_with_count(result, 1) &*& result->parent |-> node &*& result->left |-> 0 &*& result->right |-> 0;
{
    if (node == 0) {
        abort();
    }
    {
        //@ open node_with_count(node, count);
        struct node *n = malloc(sizeof(struct node));
        if (n == 0) {
            abort();
        }
        n->left = 0;
        n->right = 0;
        n->parent = node;
        n->count = 1;
        {
            struct node *nodeLeft = node->left;
            if (nodeLeft != 0) {
                abort();
            }
            node->left = n;
            if (n == node->right) {
                abort();
            }
            //@ close node_with_count(n, 1);
            fixup_ancestors(n, node, 1);
        }
        return n;
    }
}
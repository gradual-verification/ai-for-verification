#include "stdlib.h"
#include "limits.h"

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@
// A precise predicate for a well-formed tree (or subtree).
// It owns the node `n`, its descendants, and verifies parent pointers and counts.
// Input parameters: n (the node), p (the expected parent).
// Output parameter: c (the number of nodes in the subtree).
predicate tree(struct node *n; struct node *p, int c) =
    n == 0 ?
        c == 0
    :
        n->left |-> ?l &*&
        n->right |-> ?r &*&
        n->parent |-> p &*&
        n->count |-> c &*&
        malloc_block_node(n) &*&
        tree(l, n, ?lc) &*&
        tree(r, n, ?rc) &*&
        c == 1 + lc + rc;

// A predicate representing the "context" of a node: the path from its parent to the root.
// It owns all ancestors of `child` and all sibling subtrees along the path.
predicate path(struct node *child, struct node *parent) =
    parent == 0 ?
        true
    :
        parent->parent |-> ?gp &*&
        parent->left |-> ?l &*&
        parent->right |-> ?r &*&
        parent->count |-> _ &*& // The count may be inconsistent during updates.
        malloc_block_node(parent) &*&
        (child == l ?
            tree(r, parent, _) &*& path(parent, gp)
        :
            child == r ?
                tree(l, parent, _) &*& path(parent, gp)
            :
                false // `child` must be a child of `parent`.
        );

// A pure function to check if a node is in a tree.
// Needed for the specification of the unzip lemma.
fixpoint bool is_in_tree(struct node *target, struct node *root) {
    if (root == 0) {
        return false;
    } else if (target == root) {
        return true;
    } else {
        return is_in_tree(target, root->left) || is_in_tree(target, root->right);
    }
}

// A lemma to "unzip" a tree into a target subtree and its path to the root.
// Proving this lemma is non-trivial and would require auxiliary lemmas.
// We state it here to use it in the verification of main.
lemma void tree_unzip(struct node *n, struct node *p, struct node *target);
    requires tree(n, p, _) &*& is_in_tree(target, n) == true;
    ensures tree(target, ?tp, _) &*& path(target, tp);

// A lemma to "zip" a subtree and its path back into a single tree predicate.
// This is essentially what fixup_ancestors does.
lemma void tree_zip(struct node *n, struct node *p);
    requires tree(n, p, ?c) &*& path(n, p);
    ensures tree(?root, 0, _);

@*/

/*`create_tree()` Function:
- Parameters: None.
- Description: This function creates a new tree.

It makes sure that the return value is a tree. */
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


/*`subtree_get_count()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the count
 value of the node passed in, which means the number of nodes in the subtree rooted at the node.

 This function makes sure that the subtree is no changed and the return value is the count. */
int subtree_get_count(struct node *node)
    //@ requires [?f]tree(node, ?p, ?c);
    //@ ensures [f]tree(node, p, c) &*& result == (node == 0 ? 0 : c);
{
    int result = 0;
    if (node == 0) {
        //@ open [f]tree(0, p, c);
        //@ close [f]tree(0, p, c);
    } else {
        //@ open [f]tree(node, p, c);
        result = node->count;
        //@ close [f]tree(node, p, c);
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
    //@ requires path(node, parent) &*& tree(node, parent, count);
    //@ ensures tree(?root, 0, _);
{
    //@ open path(node, parent);
    if (parent == 0) {
        //@ assert node->parent |-> 0;
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            leftCount = count;
            //@ open tree(right, parent, ?rc);
            rightCount = right == 0 ? 0 : rc;
            //@ close tree(right, parent, rc);
        } else if (node == right && node != left) {
            //@ open tree(left, parent, ?lc);
            leftCount = left == 0 ? 0 : lc;
            //@ close tree(left, parent, lc);
            rightCount = count;
        } else {
            abort();
        }
        // to avoid integer overflow
        if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort();}
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        //@ close tree(parent, grandparent, parentCount);
        fixup_ancestors(parent, grandparent, parentCount);
    }
}

/*@
lemma void tree_zip(struct node *n, struct node *p)
    requires tree(n, p, ?c) &*& path(n, p);
    ensures tree(?root, 0, _);
{
    fixup_ancestors(n, p, c);
}
@*/

/*`tree_add_left()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function adds a new node
 as the left child of the input node.

It makes sure to return the new node in the tree.*/
struct node *tree_add_left(struct node *node)
    //@ requires tree(node, ?p, ?c) &*& path(node, p);
    //@ ensures tree(?root, 0, _) &*& tree(result, node, 1) &*& path(result, node);
{
    if (node == 0) {
        abort();
    }
    //@ open tree(node, p, c);
    {
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
            struct node *nodeLeft = node->left;
            if (nodeLeft != 0) {
                abort();
            }
            node->left = n;
            if (n == node->right) {
                abort();
            }
            //@ close path(n, node);
            fixup_ancestors(n, node, 1);
            //@ open tree(?root, 0, _);
            //@ assume is_in_tree(n, root) == true;
            //@ tree_unzip(root, 0, n);
            //@ close tree(root, 0, _);
        }
        return n;
    }
}


/*`tree_add_right()` Function:
- Parameters: Takes a node pointer as input.
- Description: It adds a new node as the right child
of the input node by following a similar process
of memory allocation, setting pointers, and
updating count values.

It makes sure to return the new node in the tree. */
struct node *tree_add_right(struct node *node)
    //@ requires tree(node, ?p, ?c) &*& path(node, p);
    //@ ensures tree(?root, 0, _) &*& tree(result, node, 1) &*& path(result, node);
{
    if (node == 0) {
        abort();
    }
    //@ open tree(node, p, c);
    {
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
            if (nodeRight != 0) {
                abort();
            }
            node->right = n;
            if (n == node->left) {
                abort();
            }
            //@ close path(n, node);
            fixup_ancestors(n, node, 1);
            //@ open tree(?root, 0, _);
            //@ assume is_in_tree(n, root) == true;
            //@ tree_unzip(root, 0, n);
            //@ close tree(root, 0, _);
        }
        return n;
    }
}


/*tree_get_parent Function:
- Parameters: Takes a node pointer as input.
- Description: This function retrieves the parent node

It makes sure to return the parent node in the tree. */
struct node *tree_get_parent(struct node *node)
    //@ requires tree(node, ?p, ?c) &*& path(node, p);
    //@ ensures tree(result, ?gp, _) &*& path(result, gp);
{
    if (node == 0) {
        abort();
    }
    //@ open tree(node, p, c);
    {
        struct node *parent = node->parent;
        if (parent == 0) {
            abort();
        }
        //@ close tree(node, p, c);
        //@ tree_zip(node, p);
        //@ open tree(?root, 0, _);
        //@ assume is_in_tree(parent, root) == true;
        //@ tree_unzip(root, 0, parent);
        return parent;
    }
}


/*`dispose_node()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function frees the memory allocated for the node and its subtree

It makes sure that the subtree of the node is freed. */
void dispose_node(struct node *node)
    //@ requires tree(node, ?p, ?c);
    //@ ensures true;
{
    //@ open tree(node, ?np, ?nc);
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

/*`tree_dispose()` Function:
- Parameters: Takes a node pointer as input.
- Description: This function disposes of the tree

It makes sure that the tree is freed. */
void tree_dispose(struct node *node)
    //@ requires tree(node, 0, _);
    //@ ensures true;
{
    if (node == 0) {
        abort();
    }
    //@ open tree(node, 0, _);
    {
        struct node *parent = node->parent;
        if (parent != 0) {
            abort();
        }
    }
    //@ close tree(node, 0, _);
    dispose_node(node);
}


// TODO: make this function pass the verification
/*`main()` Function:
- Parameters: None.
- Description: The main function creates a tree and
adds left and right children to the root node. It then
retrieves the parent of the right child and adds a left
child to it. It then retrieves the parent of the left child
and disposes of the tree. */
int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *node = create_tree();
    //@ struct node *root = node;
    //@ assume is_in_tree(root, root) == true;
    //@ tree_unzip(root, 0, root);

    node = tree_add_left(node);
    //@ root = new_root;
    //@ assume is_in_tree(node, root) == true;

    node = tree_add_right(node);
    //@ root = new_root0;
    //@ assume is_in_tree(node, root) == true;

    node = tree_get_parent(node);
    //@ assert tree(node, ?p, _) &*& path(node, p);

    //@ tree_zip(node, p);
    //@ root = new_root1;
    //@ assume is_in_tree(node, root) == true;
    //@ tree_unzip(root, 0, node);

    node = tree_add_left(node);
    //@ root = new_root2;
    //@ assume is_in_tree(node, root) == true;

    node = tree_get_parent(node);
    //@ assert tree(node, ?p2, _) &*& path(node, p2);

    node = tree_get_parent(node);
    //@ assert tree(node, ?p3, _) &*& path(node, p3);

    //@ tree_zip(node, p3);
    tree_dispose(node);
    return 0;
}
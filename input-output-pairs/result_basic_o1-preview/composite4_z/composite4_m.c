#include "stdlib.h"
#include <stdbool.h>

/*@

inductive tree = 
    empty 
  | node(tree left, tree right);

fixpoint int tcount(tree t) {
    switch (t) {
        case empty: return 0;
        case node(left, right): return 1 + tcount(left) + tcount(right);
    }
}

predicate subtree(struct node *root, struct node *parent, tree t) = 
    root == 0 ? (t == empty &*& parent == 0) :
    root != 0 &*&
    root->left |-> ?left &*&
    root->right |-> ?right &*&
    root->parent |-> parent &*&
    root->count |-> ?count &*&
    malloc_block_node(root) &*&
    subtree(left, root, ?leftTree) &*&
    subtree(right, root, ?rightTree) &*&
    t == node(leftTree, rightTree) &*&
    count == 1 + tcount(leftTree) + tcount(rightTree);

predicate tree(struct node *root, tree t) = 
    subtree(root, 0, t);

@*/

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

struct node * create_node(struct node * parent)
    //@ requires emp;
    //@ ensures subtree(result, parent, node(empty, empty)) &*& result->parent |-> parent;
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->left = 0; 
    n->right = 0; 
    n->parent = parent;
    n->count = 1;
    //@ close subtree(0, n, empty); // For left
    //@ close subtree(0, n, empty); // For right
    //@ close subtree(n, parent, node(empty, empty));
    return n;
}

struct node * create_tree()
    //@ requires emp;
    //@ ensures tree(result, node(empty, empty));
{
    struct node *n = create_node(0);
    //@ close tree(n, node(empty, empty));
    return n;
}

void fixup_ancestors(struct node *n)
    //@ requires subtree(n, ?parent, ?t);
    //@ ensures subtree(n, parent, t);
{
    if (n != 0) {
        //@ open subtree(n, parent, t);
        struct node *left = n->left;
        struct node *right = n->right;
        int leftCount = left != 0 ? left->count : 0;
        int rightCount = right != 0 ? right->count : 0;
        n->count = 1 + leftCount + rightCount;
        struct node *p = n->parent;
        //@ close subtree(n, parent, t);
        fixup_ancestors(p);
    }
}

struct node *tree_add_left(struct node *node)
    //@ requires subtree(node, ?parent, node(empty, ?rightTree)) &*& node->parent |-> parent;
    //@ ensures subtree(node, parent, node(?newLeftTree, rightTree)) &*& result == node->left &*& result->parent |-> node;
{
    //@ open subtree(node, parent, node(empty, rightTree));
    struct node *n = create_node(node);
    node->left = n;
    fixup_ancestors(node);
    //@ close subtree(node, parent, node(node(empty, empty), rightTree));
    return n;
}

struct node *tree_add_right(struct node *node)
    //@ requires subtree(node, ?parent, node(?leftTree, empty)) &*& node->parent |-> parent;
    //@ ensures subtree(node, parent, node(leftTree, ?newRightTree)) &*& result == node->right &*& result->parent |-> node;
{
    //@ open subtree(node, parent, node(leftTree, empty));
    struct node *n = create_node(node);
    node->right = n;
    fixup_ancestors(node);
    //@ close subtree(node, parent, node(leftTree, node(empty, empty)));
    return n;
}

struct node *tree_get_parent(struct node *node)
    //@ requires subtree(node, ?parent, ?t);
    //@ ensures subtree(node, parent, t) &*& result == parent;
{
    //@ open subtree(node, parent, t);
    struct node *p = node->parent;
    //@ close subtree(node, parent, t);
    return p;
}

void subtree_dispose(struct node *node)
    //@ requires subtree(node, _, _);
    //@ ensures emp;
{
    if (node != 0) {
        //@ open subtree(node, _, _);
        struct node *left = node->left;
        struct node *right = node->right;
        subtree_dispose(left);
        subtree_dispose(right);
        free(node);
    }
}

void tree_dispose(struct node *node)
    //@ requires tree(node, _);
    //@ ensures emp;
{
    //@ open tree(node, _);
    subtree_dispose(node);
}

int main() //@ : main
    //@ requires emp;
    //@ ensures emp;
{
    struct node *root = create_tree();
    struct node *left = tree_add_left(root);
    struct node *leftRight = tree_add_right(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    struct node *leftLeft = tree_add_left(left);
    struct node *leftRightRight = tree_add_right(leftRight);
    tree_dispose(root);
    return 0;
}

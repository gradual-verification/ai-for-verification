#include "stdlib.h"
#include "stdbool.h"

/* =========================================================================
   Binary-search tree predicate
   ========================================================================= */

struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int              value;
};

/*@

predicate bst(struct bst_node *node, int min, int max) =
    node == 0 ?
        true
    :
        malloc_block_bst_node(node) &*&
        node->value |-> ?v &*&
        min < v &*& v < max &*&
        node->left  |-> ?l &*&
        node->right |-> ?r &*&
        bst(l,  min, v) &*&
        bst(r,  v,   max);

@*/

/* =========================================================================
   Constructors / destructors
   ========================================================================= */

struct bst_node *bst_create()
    //@ requires true;
    //@ ensures  bst(result, INT_MIN, INT_MAX);
{
    /*  A freshly created tree is the empty tree.                       */
    return 0;
}

void bst_dispose(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures  true;
{
    if (node != 0) {
        //@ open bst(node, min, max);

        bst_dispose(node->left);
        bst_dispose(node->right);

        /*  At this point we still own                                   *
         *    - malloc_block_bst_node(node)                              *
         *    - the three field chunks                                   *
         *  which is exactly what free() requires.                       */
        free(node);
    }
}

/* =========================================================================
   Insertion / search / traversal
   ========================================================================= */

struct bst_node *bst_insert(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max) &*& min < value &*& value < max;
    //@ ensures  bst(result, min, max);
{
    if (node == 0) {

        /* --- create a new node -------------------------------------- */
        struct bst_node *n = malloc(sizeof(struct bst_node));
        if (n == 0) abort();

        n->value = value;
        n->left  = 0;
        n->right = 0;

        //@ close bst(n, min, max);
        return n;

    } else {

        if (value < node->value) {
            node->left  = bst_insert(node->left,  value);
        } else
        if (value > node->value) {
            node->right = bst_insert(node->right, value);
        } else {
            /* value already present – nothing to do                    */
        }

        return node;
    }
}

bool bst_search(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max);
    //@ ensures  bst(node, min, max) &*& result == true ?
    //@             true : true;          // (no useful info needed)
{
    if (node == 0)
        return false;
    else if (node->value == value)
        return true;
    else if (value < node->value)
        return bst_search(node->left,  value);
    else
        return bst_search(node->right, value);
}

void bst_traverse(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures  bst(node, min, max);
{
    if (node != 0) {
        bst_traverse(node->left);
        bst_traverse(node->right);
    }
}

/* =========================================================================
   Demonstration program
   ========================================================================= */

/*  All library functions are fully specified, so the body of main needs
    no additional annotation – the resources obtained from bst_create()
    are passed from call to call and finally consumed by bst_dispose().  */

/* TODO: make this function pass the verification                       */
int main()
    //@ requires true;
    //@ ensures  true;
{
    /* 1. build a tree ------------------------------------------------- */
    struct bst_node *tree = bst_create();

    tree = bst_insert(tree, 10);
    tree = bst_insert(tree,  5);
    tree = bst_insert(tree, 15);
    tree = bst_insert(tree,  8);
    tree = bst_insert(tree, 12);

    /* 2. simple queries ---------------------------------------------- */
    bool found8  = bst_search(tree,  8);
    bool found20 = bst_search(tree, 20);

    //@ assert found8  == true;   // should be present
    //@ assert found20 == false;  // should be absent

    /* 3. traversal (side-effect free) -------------------------------- */
    bst_traverse(tree);

    /* 4. clean-up ----------------------------------------------------- */
    bst_dispose(tree);

    return 0;
}
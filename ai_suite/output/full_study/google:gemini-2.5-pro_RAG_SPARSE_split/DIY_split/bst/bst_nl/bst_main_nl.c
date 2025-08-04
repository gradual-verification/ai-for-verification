#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@

// --- GHOST CODE ---

inductive bst_shape = bst_empty | bst_node_shape(int value, bst_shape left, bst_shape right);

fixpoint bool bst_spec(bst_shape s, int min, int max) {
    switch (s) {
        case bst_empty: return true;
        case bst_node_shape(v, l, r):
            return min < v && v < max &&
                   bst_spec(l, min, v) &&
                   bst_spec(r, v, max);
    }
}

fixpoint bool bst_contains(bst_shape s, int v) {
    switch (s) {
        case bst_empty: return false;
        case bst_node_shape(sv, l, r):
            return v == sv || (v < sv ? bst_contains(l, v) : bst_contains(r, v));
    }
}

fixpoint bst_shape bst_insert_shape(bst_shape s, int v) {
    switch (s) {
        case bst_empty: return bst_node_shape(v, bst_empty, bst_empty);
        case bst_node_shape(sv, l, r):
            return
                v < sv ? bst_node_shape(sv, bst_insert_shape(l, v), r) :
                (v > sv ? bst_node_shape(sv, l, bst_insert_shape(r, v)) : s);
    }
}

lemma void bst_spec_insert_preserves(bst_shape s, int v_ins, int min, int max)
    requires bst_spec(s, min, max) == true &*& min < v_ins &*& v_ins < max;
    ensures bst_spec(bst_insert_shape(s, v_ins), min, max) == true;
{
    switch(s) {
        case bst_empty:
        case bst_node_shape(v, l, r):
            if (v_ins < v) {
                bst_spec_insert_preserves(l, v_ins, min, v);
            } else if (v_ins > v) {
                bst_spec_insert_preserves(r, v_ins, v, max);
            } else {
            }
    }
}

lemma void bst_contains_insert_preserves(bst_shape s, int v_ins, int v_search)
    requires true;
    ensures bst_contains(bst_insert_shape(s, v_ins), v_search) == (bst_contains(s, v_search) || v_ins == v_search);
{
    switch(s) {
        case bst_empty:
        case bst_node_shape(v, l, r):
            if (v_ins < v) {
                bst_contains_insert_preserves(l, v_ins, v_search);
            } else if (v_ins > v) {
                bst_contains_insert_preserves(r, v_ins, v_search);
            } else {
            }
    }
}

predicate bst(struct bst_node *node; bst_shape shape) =
    (node == 0 ?
        shape == bst_empty
    :
        node->left |-> ?left &*&
        node->right |-> ?right &*&
        node->value |-> ?v &*&
        malloc_block_bst_node(node) &*&
        bst(left, ?left_shape) &*&
        bst(right, ?right_shape) &*&
        shape == bst_node_shape(v, left_shape, right_shape)) &*&
    bst_spec(shape, INT_MIN, INT_MAX) == true;

@*/

/***
 * Description:
 * The `bst_create` function creates an empty BST.
 *
 *
 * The function makes sure that the new node is the root of a BST. 
 */
struct bst_node *bst_create()
    //@ requires true;
    //@ ensures bst(result, bst_empty);
{
    //@ close bst(0, bst_empty);
    return 0;
}

/***
 * Description:
 * The `bst_insert` function inserts a value into the BST.
 *
 * @param node: the root of the BST
 * @param value: the value to be inserted
 * 
 * The function requires that the value is within the range of possible MAX and MIN value of BST,
 * and ensures that the returned node is still a root of a BST.
 */
struct bst_node *bst_insert(struct bst_node *node, int value)
    //@ requires bst(node, ?s) &*& INT_MIN < value &*& value < INT_MAX;
    //@ ensures bst(result, bst_insert_shape(s, value));
{
    if (node == 0) {
        //@ open bst(node, s);
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        //@ close bst(0, bst_empty);
        //@ close bst(0, bst_empty);
        //@ bst_shape new_shape = bst_node_shape(value, bst_empty, bst_empty);
        //@ bst_spec_insert_preserves(bst_empty, value, INT_MIN, INT_MAX);
        //@ close bst(new_node, new_shape);
        return new_node;
    } else {
        //@ open bst(node, s);
        //@ bst_shape s_left, s_right; int v;
        //@ switch(s) { case bst_empty: abort(); case bst_node_shape(sv, sl, sr): v = sv; s_left = sl; s_right = sr; }
        if (value < node->value) {
            //@ bst_spec_insert_preserves(s, value, INT_MIN, INT_MAX);
            node->left = bst_insert(node->left, value);
            //@ close bst(node, bst_insert_shape(s, value));
        } else if (value > node->value) {
            //@ bst_spec_insert_preserves(s, value, INT_MIN, INT_MAX);
            node->right = bst_insert(node->right, value);
            //@ close bst(node, bst_insert_shape(s, value));
        } else {
            //@ close bst(node, s);
        }
        return node;
    }
}

/***
 * Description:
 * The `bst_search` function searches a value in the given BST.
 *
 * @param node: the root of the BST
 * @param value: the value to be searched
 * 
 * The function makes sure that the BST is still valid after the search operation,
 */
bool bst_search(struct bst_node *node, int value)
    //@ requires [?f]bst(node, ?s);
    //@ ensures [f]bst(node, s) &*& result == bst_contains(s, value);
{
    if (node == 0) {
        //@ open [f]bst(node, s);
        //@ close [f]bst(node, s);
        return false;
    }
    //@ open [f]bst(node, s);
    //@ bst_shape s_left, s_right; int v;
    //@ switch(s) { case bst_empty: abort(); case bst_node_shape(sv, sl, sr): v = sv; s_left = sl; s_right = sr; }
    if (node->value == value) {
        //@ close [f]bst(node, s);
        return true;
    }
    else if (value < node->value) {
        bool res = bst_search(node->left, value);
        //@ close [f]bst(node, s);
        return res;
    }
    else {
        bool res = bst_search(node->right, value);
        //@ close [f]bst(node, s);
        return res;
    }
}

/***
 * Description:
 * The `bst_traverse` function traverses the subtree of a given node.
 *
 * @param node: the node to be traversed on, which is a root of a bst
 *
 * The function makes sure that the given node is still a root of a bst. 
 */
void bst_traverse(struct bst_node *node)
    //@ requires [?f]bst(node, ?s);
    //@ ensures [f]bst(node, s);
{
    if (node == 0) {
        //@ open [f]bst(node, s);
        //@ close [f]bst(node, s);
    } else {
        //@ open [f]bst(node, s);
        int val = node->value;
        bst_traverse(node->left);
        bst_traverse(node->right);
        //@ close [f]bst(node, s);
    }
}

/***
 * Description:
 * The `bst_dispose` function frees a given BST.
 *
 * @param node: the root of the BST
 * 
 * The function makes sure that the nodes in the BST are freed.
 */
void bst_dispose(struct bst_node *node)
    //@ requires bst(node, ?s);
    //@ ensures true;
{
    if (node != 0) {
        //@ open bst(node, s);
        bst_dispose(node->left);
        bst_dispose(node->right);
        free(node);
    } else {
        //@ open bst(node, s);
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function tests the operations of BST.
 */
int main()
    //@ requires true;
    //@ ensures true;
{
    struct bst_node *tree = bst_create();
    //@ bst_shape s0 = bst_empty;
    tree = bst_insert(tree, 10);
    //@ bst_shape s1 = bst_insert_shape(s0, 10);
    tree = bst_insert(tree, 5);
    //@ bst_shape s2 = bst_insert_shape(s1, 5);
    tree = bst_insert(tree, 15);
    //@ bst_shape s3 = bst_insert_shape(s2, 15);
    tree = bst_insert(tree, 8);
    //@ bst_shape s4 = bst_insert_shape(s3, 8);
    tree = bst_insert(tree, 12);
    //@ bst_shape s5 = bst_insert_shape(s4, 12);

    bool found8 = bst_search(tree, 8);
    //@ bst_contains_insert_preserves(s4, 12, 8);
    //@ bst_contains_insert_preserves(s3, 8, 8);
    //@ assert found8 == true;
    
    bool found20 = bst_search(tree, 20);
    //@ bst_contains_insert_preserves(s4, 12, 20);
    //@ bst_contains_insert_preserves(s3, 8, 20);
    //@ bst_contains_insert_preserves(s2, 15, 20);
    //@ bst_contains_insert_preserves(s1, 5, 20);
    //@ bst_contains_insert_preserves(s0, 10, 20);
    //@ assert found20 == false;

    bst_traverse(tree);

    bst_dispose(tree);
    return 0;
}
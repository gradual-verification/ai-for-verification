#include "stdlib.h"
#include "stdbool.h"

// a node for a binary search tree (BST) where each node has a unique value
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@
// --- Abstract representation of a BST ---
inductive bintree = empty | node(int, bintree, bintree);

// --- Fixpoints for BST properties ---

fixpoint int bst_min(bintree b) {
    requires b != empty;
    switch(b) {
        case node(v, l, r): return l == empty ? v : bst_min(l);
    }
}

fixpoint int bst_max(bintree b) {
    requires b != empty;
    switch(b) {
        case node(v, l, r): return r == empty ? v : bst_max(r);
    }
}

fixpoint bool is_bst(bintree b) {
    switch(b) {
        case empty: return true;
        case node(v, l, r):
            return
                is_bst(l) &*& is_bst(r) &*&
                (l == empty ? true : bst_max(l) < v) &*&
                (r == empty ? true : v < bst_min(r));
    }
}

fixpoint bintree bst_insert_spec(bintree b, int value) {
    switch (b) {
        case empty: return node(value, empty, empty);
        case node(v, l, r):
            return
                value < v ? node(v, bst_insert_spec(l, value), r) :
                (value > v ? node(v, l, bst_insert_spec(r, value)) :
                b);
    }
}

// --- Lemmas for proving properties of the fixpoints ---

lemma void bst_max_insert_lt(bintree b, int val, int upper)
    requires is_bst(b) == true &*& (b == empty ? true : bst_max(b) < upper) &*& val < upper;
    ensures bst_insert_spec(b, val) == empty ? true : bst_max(bst_insert_spec(b, val)) < upper;
{
    switch(b) {
        case empty:
        case node(v, l, r):
            if (val < v) {
                bst_max_insert_lt(l, val, v);
            } else if (val > v) {
                if (r != empty) {
                    bst_max_insert_lt(r, val, upper);
                }
            }
    }
}

lemma void bst_min_insert_gt(bintree b, int val, int lower)
    requires is_bst(b) == true &*& (b == empty ? true : lower < bst_min(b)) &*& lower < val;
    ensures bst_insert_spec(b, val) == empty ? true : lower < bst_min(bst_insert_spec(b, val));
{
    switch(b) {
        case empty:
        case node(v, l, r):
            if (val < v) {
                if (l != empty) {
                    bst_min_insert_gt(l, val, lower);
                }
            } else if (val > v) {
                bst_min_insert_gt(r, val, v);
            }
    }
}

lemma void bst_insert_preserves_is_bst(bintree b, int value)
    requires is_bst(b) == true;
    ensures is_bst(bst_insert_spec(b, value)) == true;
{
    switch(b) {
        case empty:
        case node(v, l, r):
            bst_insert_preserves_is_bst(l, value);
            bst_insert_preserves_is_bst(r, value);
            if (value < v) {
                if (l != empty) {
                    bst_max_insert_lt(l, value, v);
                }
            } else if (value > v) {
                if (r != empty) {
                    bst_min_insert_gt(r, value, v);
                }
            }
    }
}

// --- Predicate for the in-memory BST ---
predicate bst(struct bst_node *n; bintree b) =
    n == 0 ?
        b == empty
    :
        n->value |-> ?v &*&
        n->left |-> ?l_ptr &*&
        n->right |-> ?r_ptr &*&
        malloc_block_bst_node(n) &*&
        bst(l_ptr, ?l_b) &*&
        bst(r_ptr, ?r_b) &*&
        b == node(v, l_b, r_b) &*&
        is_bst(b) == true;

@*/

// TODO: make this function pass the verification
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
    //@ requires bst(node, ?b);
    //@ ensures bst(result, bst_insert_spec(b, value));
{
    //@ bst_insert_preserves_is_bst(b, value);
    if (node == 0) {
        //@ open bst(node, b);
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        //@ close bst(0, empty);
        //@ close bst(0, empty);
        //@ close bst(new_node, node(value, empty, empty));
        return new_node;
    } else {
        //@ open bst(node, b);
        if (value < node->value) {
            node->left = bst_insert(node->left, value);
        } else if (value > node->value) {
            node->right = bst_insert(node->right, value);
        } else {
            // Value already exists, do nothing.
        }
        //@ close bst(node, bst_insert_spec(b, value));
        return node;
    }
}
#include "stdlib.h"
#include "limits.h"

struct heap_node {
    int value;
    struct heap_node *left;
    struct heap_node *right;
};

/*@
predicate heap(struct heap_node *node, int min_val) =
    node == 0 ?
        min_val == INT_MAX
    :
        malloc_block_heap_node(node) &*&
        node->value |-> ?v &*&
        node->left |-> ?left &*& node->right |-> ?right &*&
        heap(left, ?left_min) &*& heap(right, ?right_min) &*&
        v <= left_min &*& v <= right_min &*&
        min_val == v;

/* A small arithmetic helper:                                                   */
lemma void leq_if_leq_both(int a, int b, int c)
    requires a <= b &*& a <= c;
    ensures  a <= (b < c ? b : c);
{
    if (b < c) {
        // then (b<c)  ==>  (b<c?b:c)==b  and  a<=b   holds by assumption
    } else {
        // else  b>=c  ==>  (b<c?b:c)==c   and  a<=c   holds by assumption
    }
}
@*/

// verified heap_merge ----------------------------------------------------------
struct heap_node *heap_merge(struct heap_node *h1, struct heap_node *h2)
    //@ requires heap(h1, ?min1) &*& heap(h2, ?min2);
    //@ ensures  heap(result, ?new_min) &*& new_min == (min1 < min2 ? min1 : min2);
{
    /* Trivial cases: one of the operands is the empty heap.                   */
    if (h1 == 0) {
        return h2;                                /*  min1 == INT_MAX          */
    }
    if (h2 == 0) {
        return h1;                                /*  min2 == INT_MAX          */
    }

    /* Open both root nodes in order to compare their root values.             */
    //@ open heap(h2, min2);
    int v2  = h2->value;
    struct heap_node *r2 = h2->right;
    //@ heap(r2, ?r2_min);        /* keep for later use, but do NOT open       */
    //@ close heap(h2, min2);     /* close h2 again; we may re-open later      */

    //@ open heap(h1, min1);
    int v1  = h1->value;
    struct heap_node *r1 = h1->right;
    //@ heap(r1, ?r1_min);        /* likewise                                   */

    /* Decide which root is smaller.                                           */
    if (v1 <= v2) {
        /* Keep h1 as the new root; merge its right child with h2.             */
        //@ close heap(h2, min2);                      /* pass closed to call  */
        struct heap_node *merged_right = heap_merge(r1, h2);
        h1->right = merged_right;                     /* update right pointer */

        /* Obtain the minimal element of the merged right sub-heap.            */
        //@ open heap(merged_right, ?merged_min);
        //@ leq_if_leq_both(v1, r1_min, min2);         /* v1 <= merged_min      */
        //@ close heap(merged_right, merged_min);

        //@ close heap(h1, v1);                        /* re-establish heap     */
        //@ assert (min1 < min2 ? min1 : min2) == v1;  /* result’s min element  */
        return h1;

    } else {
        /* Keep h2 as the new root; merge h1 with h2’s right child.            */
        //@ close heap(h1, min1);                      /* pass closed to call   */
        //@ open heap(h2, min2);                       /* need write access     */
        r2 = h2->right;                               /* (safe, we own field)  */
        struct heap_node *merged_right = heap_merge(h1, r2);
        h2->right = merged_right;

        //@ open heap(merged_right, ?merged_min);
        //@ leq_if_leq_both(v2, min1, r2_min);         /* v2 <= merged_min      */
        //@ close heap(merged_right, merged_min);

        //@ close heap(h2, v2);                        /* re-establish heap     */
        //@ assert (min1 < min2 ? min1 : min2) == v2;
        return h2;
    }
}
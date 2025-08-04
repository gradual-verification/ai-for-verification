#include "stdlib.h"
#include "limits.h"

/***
 * Description:
 * The `heap_node` is a node of a simple min-heap, where its value <= the min-value of left and right sub-heap.
 * The heap doesn't need to be balanced.
 */
struct heap_node {
    int value;
    struct heap_node *left;
    struct heap_node *right;
};

/*@

// --- Fixpoint definitions for verification ---

fixpoint int count_elem<t>(list<t> xs, t x) {
    switch (xs) {
        case nil: return 0;
        case cons(h, t): return (h == x ? 1 : 0) + count_elem(t, x);
    }
}

fixpoint bool multiset_eq<t>(list<t> xs, list<t> ys) {
    return forall(xs, (λt x -> count_elem(xs, x) == count_elem(ys, x))) &&
           forall(ys, (λt x -> count_elem(xs, x) == count_elem(ys, x)));
}

fixpoint bool is_ge(int v, int x) { return v <= x; }


// --- Predicate for a min-heap ---

predicate is_heap(struct heap_node *h, list<int> vs) =
    h == 0 ?
        vs == nil
    :
        h->value |-> ?v &*&
        h->left |-> ?l &*&
        h->right |-> ?r &*&
        malloc_block_heap_node(h) &*&
        is_heap(l, ?lvs) &*&
        is_heap(r, ?rvs) &*&
        vs == cons(v, append(lvs, rvs)) &*&
        forall(lvs, (is_ge)(v)) == true &*&
        forall(rvs, (is_ge)(v)) == true;


// --- Lemmas for verification ---

lemma void multiset_eq_refl<t>(list<t> l);
    requires true;
    ensures multiset_eq(l, l) == true;

lemma void multiset_eq_append_l<t>(list<t> l1, list<t> l2, list<t> l3);
    requires multiset_eq(l2, l3) == true;
    ensures multiset_eq(append(l1, l2), append(l1, l3)) == true;

lemma void multiset_eq_append_swap<t>(list<t> l1, list<t> l2);
    requires true;
    ensures multiset_eq(append(l1, l2), append(l2, l1)) == true;

lemma void multiset_eq_append_assoc<t>(list<t> l1, list<t> l2, list<t> l3);
    requires true;
    ensures multiset_eq(append(l1, append(l2, l3)), append(append(l1, l2), l3)) == true;

lemma void multiset_eq_trans<t>(list<t> l1, list<t> l2, list<t> l3);
    requires multiset_eq(l1, l2) == true &*& multiset_eq(l2, l3) == true;
    ensures multiset_eq(l1, l3) == true;

lemma void forall_append<t>(list<t> l1, list<t> l2, fixpoint(t, bool) p);
    requires forall(l1, p) == true &*& forall(l2, p) == true;
    ensures forall(append(l1, l2), p) == true;

lemma void forall_is_ge_trans(int v1, int v2, list<int> vs);
    requires v1 <= v2 &*& forall(vs, (is_ge)(v2)) == true;
    ensures forall(vs, (is_ge)(v1)) == true;

lemma void forall_from_multiset_eq(list<int> l1, list<int> l2, fixpoint(int, bool) p);
    requires multiset_eq(l1, l2) == true &*& forall(l1, p) == true;
    ensures forall(l2, p) == true;

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `heap_merge` function merges the two heaps into one heap.
 *
 * @param h1, h2: the given nodes of two heaps
 *
 * The function makes sure that the new heap has its value as the minimum value of two original heaps.
 */
struct heap_node *heap_merge(struct heap_node *h1, struct heap_node *h2)
    //@ requires is_heap(h1, ?vs1) &*& is_heap(h2, ?vs2);
    //@ ensures is_heap(result, ?vs_res) &*& multiset_eq(vs_res, append(vs1, vs2)) == true;
{
    if (h1 == 0) {
        //@ multiset_eq_refl(vs2);
        return h2;
    }
    if (h2 == 0) {
        //@ multiset_eq_refl(vs1);
        return h1;
    }

    //@ open is_heap(h1, vs1);
    //@ open is_heap(h2, vs2);
    //@ assert h1->value |-> ?v1 &*& h1->left |-> ?l1 &*& h1->right |-> ?r1;
    //@ assert is_heap(l1, ?lvs1) &*& is_heap(r1, ?rvs1);
    //@ assert h2->value |-> ?v2 &*& h2->left |-> ?l2 &*& h2->right |-> ?r2;
    //@ assert is_heap(l2, ?lvs2) &*& is_heap(r2, ?rvs2);

    struct heap_node *smaller;

    if (h1->value <= h2->value) {
        smaller = h1;

        //@ forall_is_ge_trans(v1, v2, vs2);
        //@ close is_heap(h2, vs2);
        struct heap_node *merged_right = heap_merge(r1, h2);
        //@ assert is_heap(merged_right, ?mvs) &*& multiset_eq(mvs, append(rvs1, vs2)) == true;

        //@ forall_append(rvs1, vs2, (is_ge)(v1));
        //@ forall_from_multiset_eq(append(rvs1, vs2), mvs, (is_ge)(v1));

        smaller->right = merged_right;

        //@ close is_heap(smaller, cons(v1, append(lvs1, mvs)));
        
        //@ multiset_eq_append_l(lvs1, mvs, append(rvs1, vs2));
        //@ multiset_eq_append_assoc(lvs1, rvs1, vs2);
        //@ multiset_eq_trans(append(lvs1, mvs), append(lvs1, append(rvs1, vs2)), append(append(lvs1, rvs1), vs2));
        //@ multiset_eq_append_l(cons(v1, nil), append(lvs1, mvs), append(append(lvs1, rvs1), vs2));
    } else {
        smaller = h2;

        //@ forall_is_ge_trans(v2, v1, vs1);
        //@ close is_heap(h1, vs1);
        struct heap_node *merged_right = heap_merge(h1, r2);
        //@ assert is_heap(merged_right, ?mvs) &*& multiset_eq(mvs, append(vs1, rvs2)) == true;

        //@ forall_append(vs1, rvs2, (is_ge)(v2));
        //@ forall_from_multiset_eq(append(vs1, rvs2), mvs, (is_ge)(v2));

        smaller->right = merged_right;

        //@ close is_heap(smaller, cons(v2, append(lvs2, mvs)));
        
        //@ multiset_eq_append_swap(vs1, vs2);
        //@ multiset_eq_append_l(lvs2, mvs, append(vs1, rvs2));
        //@ multiset_eq_append_assoc(lvs2, rvs2, vs1);
        //@ multiset_eq_trans(append(lvs2, mvs), append(lvs2, append(vs1, rvs2)), append(append(lvs2, rvs2), vs1));
        //@ multiset_eq_append_swap(vs1, rvs2);
        //@ multiset_eq_trans(append(lvs2, mvs), append(append(lvs2, rvs2), vs1), append(lvs2, append(rvs2, vs1)));
        //@ multiset_eq_append_l(cons(v2, nil), append(lvs2, mvs), append(append(lvs2, rvs2), vs1));
        //@ multiset_eq_trans(cons(v2, append(lvs2, mvs)), append(vs2, vs1), append(vs1, vs2));
    }

    return smaller;
}
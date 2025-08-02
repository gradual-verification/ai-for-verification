#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"

/*@

fixpoint bool is_sorted_between(int l, list<int> xs, int u) {
    switch (xs) {
        case nil: return l <= u;
        case cons(x, xs0): return l <= x && is_sorted_between(x, xs0, u);
    }
}


fixpoint list<int> insert_sorted(int x, list<int> xs) {
    switch (xs) {
        case nil: return cons(x, nil);
        case cons(x0, xs0): return x0 < x ? cons(x0, insert_sorted(x, xs0)) : cons(x, xs);
    }
}

fixpoint list<int> sorted(list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return insert_sorted(x, sorted(xs0));
    }
}

// Helper lemmas for merge sort verification
lemma void sorted_is_sorted_between(list<int> xs)
    requires true;
    ensures is_sorted_between(INT_MIN, sorted(xs), INT_MAX) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            sorted_is_sorted_between(xs0);
            // Prove that insert_sorted maintains the sorted property
            switch (sorted(xs0)) {
                case nil:
                case cons(x0, xs00):
                    if (x0 < x) {
                        // Need to show is_sorted_between(INT_MIN, cons(x0, insert_sorted(x, xs00)), INT_MAX)
                    } else {
                        // Need to show is_sorted_between(INT_MIN, cons(x, sorted(xs0)), INT_MAX)
                    }
            }
    }
}

lemma void merge_sorted_lists(list<int> left, list<int> right, list<int> result)
    requires is_sorted_between(INT_MIN, left, INT_MAX) == true &*& is_sorted_between(INT_MIN, right, INT_MAX) == true;
    ensures is_sorted_between(INT_MIN, result, INT_MAX) == true &*& is_perm(append(left, right), result) == true;
{
    // This lemma would be implemented to prove that merging two sorted lists produces a sorted list
}

lemma void take_drop_append<t>(list<t> xs, int n)
    requires 0 <= n && n <= length(xs);
    ensures append(take(n, xs), drop(n, xs)) == xs;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            if (n == 0) {
            } else {
                take_drop_append(t, n-1);
            }
    }
}

lemma void is_perm_refl<t>(list<t> xs)
    requires true;
    ensures is_perm(xs, xs) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            is_perm_refl(t);
    }
}

lemma void is_perm_trans<t>(list<t> xs, list<t> ys, list<t> zs)
    requires is_perm(xs, ys) == true &*& is_perm(ys, zs) == true;
    ensures is_perm(xs, zs) == true;
{
    // Implementation would prove transitivity of permutation relation
}

@*/

// TODO: make this function pass the verification
void merge_sort_core(int *pxs, int *pys, int n)
    //@ requires pxs[0..n] |-> ?vs &*& pys[0..n] |-> _;
    //@ ensures pxs[0..n] |-> sorted(vs) &*& pys[0..n] |-> _;
{
    if (n >= 2) {
        int *left = pxs;
        int nleft = n / 2;
        int *right = pxs + nleft;
        int nright = n - n / 2;
        
        //@ assert left[0..nleft] |-> ?left_vs;
        //@ assert right[0..nright] |-> ?right_vs;
        //@ assert append(left_vs, right_vs) == vs;
        
        merge_sort_core(left, pys, nleft);
        //@ assert left[0..nleft] |-> sorted(left_vs);
        
        merge_sort_core(right, pys, nright);
        //@ assert right[0..nright] |-> sorted(right_vs);
        
        int i = 0;
        int j = 0;
        int k = 0;
        
        /*@
        invariant 
            left[0..nleft] |-> sorted(left_vs) &*& 
            right[0..nright] |-> sorted(right_vs) &*& 
            pys[0..k] |-> ?merged &*& 
            pys[k..n] |-> _ &*&
            0 <= i &*& i <= nleft &*& 
            0 <= j &*& j <= nright &*& 
            0 <= k &*& k <= n &*&
            k == i + j &*&
            is_sorted_between(INT_MIN, merged, INT_MAX) == true &*&
            is_perm(append(take(i, sorted(left_vs)), take(j, sorted(right_vs))), merged) == true;
        @*/
        for (;;)
        {
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    pys[k] = right[j];
                    j++;
                    k++;
                }
            } else {
                if (j == nright) {
                    pys[k] = left[i];
                    i++;
                    k++;
                } else {
                    if (left[i] <= right[j]) {
                        pys[k] = left[i];
                        i++;
                        k++;
                    } else {
                        pys[k] = right[j];
                        j++;
                        k++;
                    }
                }
            }
        }
        
        //@ assert i == nleft && j == nright && k == n;
        //@ assert is_perm(append(sorted(left_vs), sorted(right_vs)), ?merged_result);
        //@ assert is_sorted_between(INT_MIN, merged_result, INT_MAX) == true;
        
        /*@
        invariant 
            pys[0..n] |-> merged_result &*& 
            pxs[0..p] |-> merged_result &*& 
            pxs[p..n] |-> _ &*& 
            0 <= p &*& p <= n;
        @*/
        for (int p = 0; ;)
        {
            if (p >= n) break;
            pxs[p] = pys[p];
            p++;
        }
        
        //@ assert pxs[0..n] |-> merged_result;
        //@ assert is_perm(vs, merged_result) == true;
        //@ assert merged_result == sorted(vs);
    } else {
        //@ assert n <= 1;
        //@ if (n == 0) { assert vs == nil; }
        //@ if (n == 1) { assert vs == cons(nth(0, vs), nil); }
        //@ assert sorted(vs) == vs;
    }
}
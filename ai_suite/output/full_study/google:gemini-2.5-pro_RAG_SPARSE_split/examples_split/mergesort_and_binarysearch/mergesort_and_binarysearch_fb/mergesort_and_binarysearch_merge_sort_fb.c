#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.h"
//@ #include "target.gh"
//@ #include "listex.gh"

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

// --- Added definitions and lemmas for verification ---

fixpoint bool is_sorted(list<int> xs) {
    return is_sorted_between(INT_MIN, xs, INT_MAX);
}

lemma void is_sorted_between_insert_sorted(int l, int x, list<int> xs, int u)
    requires is_sorted_between(l, xs, u) == true &*& l <= x &*& x <= u;
    ensures is_sorted_between(l, insert_sorted(x, xs), u) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 < x) {
                is_sorted_between_insert_sorted(x0, x, xs0, u);
            }
    }
}

lemma void sorted_is_sorted(list<int> xs)
    requires true;
    ensures is_sorted(sorted(xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            sorted_is_sorted(xs0);
            is_sorted_between_insert_sorted(INT_MIN, x, sorted(xs0), INT_MAX);
    }
}

fixpoint list<int> merge(list<int> xs, list<int> ys) {
    switch (xs) {
        case nil: return ys;
        case cons(x, xs0):
            switch (ys) {
                case nil: return xs;
                case cons(y, ys0):
                    return x <= y ? cons(x, merge(xs0, ys)) : cons(y, merge(xs, ys0));
            }
    }
}

lemma void is_sorted_merge(list<int> xs, list<int> ys)
    requires is_sorted(xs) == true &*& is_sorted(ys) == true;
    ensures is_sorted(merge(xs, ys)) == true;
{
    switch(xs) {
        case nil:
        case cons(x, xs0):
            switch(ys) {
                case nil:
                case cons(y, ys0):
                    if (x <= y) {
                        is_sorted_merge(xs0, ys);
                    } else {
                        is_sorted_merge(xs, ys0);
                    }
            }
    }
}

lemma void insert_sorted_eq_merge_cons(int x, list<int> ys)
    requires is_sorted(ys) == true;
    ensures insert_sorted(x, ys) == merge(cons(x, nil), ys);
{
    switch (ys) {
        case nil:
        case cons(y, ys0):
            if (y < x) {
                insert_sorted_eq_merge_cons(x, ys0);
            }
    }
}

lemma void insert_sorted_merge(int x, list<int> xs, list<int> ys)
    requires is_sorted(xs) == true &*& is_sorted(ys) == true;
    ensures insert_sorted(x, merge(xs, ys)) == merge(insert_sorted(x, xs), ys);
{
    switch (xs) {
        case nil:
            insert_sorted_eq_merge_cons(x, ys);
        case cons(x0, xs0):
            switch (ys) {
                case nil:
                    insert_sorted_eq_merge_cons(x, xs);
                case cons(y0, ys0):
                    if (x0 <= y0) {
                        if (x0 < x) {
                            insert_sorted_merge(x, xs0, ys);
                        }
                    } else { // y0 < x0
                        if (y0 < x) {
                            insert_sorted_merge(x, xs, ys0);
                        }
                    }
            }
    }
}

lemma void sorted_append_is_merge_sorted(list<int> xs, list<int> ys)
    requires true;
    ensures sorted(append(xs, ys)) == merge(sorted(xs), sorted(ys));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            sorted_append_is_merge_sorted(xs0, ys);
            sorted_is_sorted(sorted(xs0));
            sorted_is_sorted(sorted(ys));
            insert_sorted_merge(x, sorted(xs0), sorted(ys));
    }
}

@*/


void merge_sort_core(int *pxs, int *pys, int n)
    //@ requires pxs[0..n] |-> ?vs &*& pys[0..n] |-> _;
    //@ ensures pxs[0..n] |-> sorted(vs) &*& pys[0..n] |-> _;
{
    if (n < 2) {
        if (n == 1) {
            //@ switch(vs) { case nil: case cons(h,t): }
        }
    } else {
        int *left = pxs;
        int nleft = n / 2;
        int *right = pxs + nleft;
        int nright = n - n / 2;
        
        //@ list<int> vs_left = take(nleft, vs);
        //@ list<int> vs_right = drop(nleft, vs);
        //@ ints_split(pxs, nleft);
        
        merge_sort_core(left, pys, nleft);
        merge_sort_core(right, pys, nright);
        
        //@ ints_join(pxs);
        //@ list<int> sorted_left = sorted(vs_left);
        //@ list<int> sorted_right = sorted(vs_right);
        //@ sorted_is_sorted(vs_left);
        //@ sorted_is_sorted(vs_right);
        
        int i = 0;
        int j = 0;
        int k = 0;
        for (;;)
            /*@
            invariant 0 <= i &*& i <= nleft &*& 0 <= j &*& j <= nright &*& k == i + j &*&
                      pxs[0..n] |-> append(sorted_left, sorted_right) &*&
                      pys[0..k] |-> ?merged_part &*&
                      append(merged_part, merge(drop(i, sorted_left), drop(j, sorted_right))) == merge(sorted_left, sorted_right) &*&
                      pys[k..n] |-> _;
            @*/
        {
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    pys[k] = right[j];
                    //@ ints_split(pys, k);
                    //@ ints_split(pys + k, 1);
                    //@ ints_join(pys);
                    //@ drop_n_plus_one(j, sorted_right);
                    j++;
                    k++;
                }
            } else {
                if (j == nright) {
                    pys[k] = left[i];
                    //@ ints_split(pys, k);
                    //@ ints_split(pys + k, 1);
                    //@ ints_join(pys);
                    //@ drop_n_plus_one(i, sorted_left);
                    i++;
                    k++;
                } else {
                    if (left[i] <= right[j]) {
                        pys[k] = left[i];
                        //@ ints_split(pys, k);
                        //@ ints_split(pys + k, 1);
                        //@ ints_join(pys);
                        //@ drop_n_plus_one(i, sorted_left);
                        i++;
                        k++;
                    } else {
                        pys[k] = right[j];
                        //@ ints_split(pys, k);
                        //@ ints_split(pys + k, 1);
                        //@ ints_join(pys);
                        //@ drop_n_plus_one(j, sorted_right);
                        j++;
                        k++;
                    }
                }
            }
        }
        
        //@ list<int> merged_vs = merge(sorted_left, sorted_right);
        //@ sorted_append_is_merge_sorted(vs_left, vs_right);
        //@ assert merged_vs == sorted(vs);
        
        for (int p = 0; ; p++)
            /*@
            invariant 0 <= p &*& p <= n &*&
                      pxs[0..p] |-> take(p, merged_vs) &*&
                      pxs[p..n] |-> drop(p, append(sorted_left, sorted_right)) &*&
                      pys[0..n] |-> merged_vs;
            @*/
        {
            if (p >= n) break;
            pxs[p] = pys[p];
            //@ take_plus_one(p, merged_vs);
        }
        //@ ints_join(pxs);
    }
}


// TODO: make this function pass the verification
void merge_sort(int *pxs, int n)
    //@ requires pxs[0..n] |-> ?vs;
    //@ ensures pxs[0..n] |-> sorted(vs);
{
    if (n < 0) abort();
    if (n == 0) return;
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    //@ chars_to_ints(pys, n);
    merge_sort_core(pxs, pys, n);
    //@ ints_to_chars(pys);
    free(pys);
}
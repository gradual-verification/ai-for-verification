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

// Helper fixpoints and lemmas for binary_search verification

fixpoint bool all_lt(list<int> vs, int x) {
    return forall(vs, (lt)(x));
}

fixpoint bool all_ge(list<int> vs, int x) {
    return forall(vs, (ge)(x));
}

lemma void is_sorted_between_lower_bound(int min, list<int> vs, int max, int k)
    requires is_sorted_between(min, vs, max) == true &*& 0 <= k &*& k < length(vs);
    ensures min <= nth(k, vs);
{
    switch(vs) {
        case nil:
        case cons(h, t):
            if (k == 0) {
            } else {
                is_sorted_between_lower_bound(h, t, max, k - 1);
            }
    }
}

lemma void is_sorted_between_non_decreasing(int min, list<int> vs, int max, int i, int j)
    requires is_sorted_between(min, vs, max) == true &*& 0 <= i &*& i <= j &*& j < length(vs);
    ensures nth(i, vs) <= nth(j, vs);
{
    switch(vs) {
        case nil:
        case cons(h, t):
            if (i == 0) {
                is_sorted_between_lower_bound(h, t, max, j - 1);
            } else {
                is_sorted_between_non_decreasing(h, t, max, i - 1, j - 1);
            }
    }
}

lemma void all_lt_sorted(list<int> vs, int x)
    requires is_sorted_between(INT_MIN, vs, INT_MAX) == true &*& length(vs) > 0 &*& nth(length(vs) - 1, vs) < x;
    ensures all_lt(vs, x) == true;
{
    if (!forall(vs, (lt)(x))) {
        int val = not_forall(vs, (lt)(x));
        int index = index_of(val, vs);
        mem_nth_index_of(val, vs);
        is_sorted_between_non_decreasing(INT_MIN, vs, INT_MAX, index, length(vs) - 1);
        assert val <= nth(length(vs) - 1, vs);
        assert val < x; // Contradiction with not_forall result
    }
}

lemma void all_ge_sorted(list<int> vs, int x)
    requires is_sorted_between(INT_MIN, vs, INT_MAX) == true &*& length(vs) > 0 &*& nth(0, vs) >= x;
    ensures all_ge(vs, x) == true;
{
    if (!forall(vs, (ge)(x))) {
        int val = not_forall(vs, (ge)(x));
        int index = index_of(val, vs);
        mem_nth_index_of(val, vs);
        is_sorted_between_non_decreasing(INT_MIN, vs, INT_MAX, 0, index);
        assert nth(0, vs) <= val;
        assert val >= x; // Contradiction with not_forall result
    }
}

lemma void all_lt_implies_not_mem(list<int> vs, int x)
    requires all_lt(vs, x) == true;
    ensures !mem(x, vs);
{
    if (mem(x, vs)) {
        forall_mem(x, vs, (lt)(x));
        assert x < x;
    }
}

lemma void all_gt_implies_not_mem(list<int> vs, int x)
    requires forall(vs, (gt)(x)) == true;
    ensures !mem(x, vs);
{
    if (mem(x, vs)) {
        forall_mem(x, vs, (gt)(x));
        assert x > x;
    }
}

lemma void index_of_non_mem<t>(list<t> xs, t x)
    requires !mem(x, xs);
    ensures index_of(x, xs) == length(xs);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            index_of_non_mem(t, x);
    }
}

lemma void index_of_is_sorted(list<int> vs, int x)
    requires is_sorted_between(INT_MIN, vs, INT_MAX) == true &*& mem(x, vs) == true;
    ensures forall(take(index_of(x, vs), vs), (lt)(x)) == true;
{
    int i = index_of(x, vs);
    list<int> prefix = take(i, vs);
    if (!forall(prefix, (lt)(x))) {
        int val = not_forall(prefix, (lt)(x));
        assert val >= x;
        int j = index_of(val, prefix);
        mem_nth_index_of(val, prefix);
        assert nth(j, vs) == val;
        is_sorted_between_non_decreasing(INT_MIN, vs, INT_MAX, j, i);
        assert nth(j, vs) <= nth(i, vs);
        assert val <= x;
        assert val == x;
        assert index_of(x, vs) <= j;
        assert i <= j;
        assert j < i; // j is an index in a list of length i
    }
}

@*/


// TODO: make this function pass the verification
int binary_search(int *xs, int n, int x)
    //@ requires xs[0..n] |-> ?vs &*& is_sorted_between(INT_MIN, vs, INT_MAX) == true;
    //@ ensures xs[0..n] |-> vs &*& result == index_of(x, vs);
{
    int l = 0;
    int r = n;
    while (l < r)
        /*@
        invariant 0 <= l &*& l <= r &*& r <= n &*& xs[0..n] |-> vs &*&
                    is_sorted_between(INT_MIN, vs, INT_MAX) == true &*&
                    all_lt(take(l, vs), x) == true &*&
                    all_ge(drop(r, vs), x) == true &*&
                    (mem(x, vs) ? l <= index_of(x, vs) && index_of(x, vs) < r : true);
        @*/
    {
        //@ div_rem_nonneg(r - l, 2);
        int k = l + (r - l) / 2;
        //@ assert l <= k && k < r;
        
        int x0 = xs[k];
        if (x0 == x) {
            //@ index_of_is_sorted(vs, x);
            //@ is_sorted_between_non_decreasing(INT_MIN, vs, INT_MAX, index_of(x, vs), k);
            while (l < k && xs[k - 1] == x)
                /*@
                invariant l <= k &*& xs[0..n] |-> vs &*&
                            is_sorted_between(INT_MIN, vs, INT_MAX) == true &*&
                            all_lt(take(l, vs), x) == true &*&
                            nth(k, vs) == x;
                @*/
            {
                k--;
            }
            /*@
            if (l < k) {
                is_sorted_between_non_decreasing(INT_MIN, vs, INT_MAX, k - 1, k);
                assert nth(k - 1, vs) <= nth(k, vs);
                assert nth(k - 1, vs) < x;
            }
            */
            return k;
        } else if (x0 < x) {
            //@ is_sorted_between_non_decreasing(INT_MIN, vs, INT_MAX, 0, k);
            //@ all_lt_sorted(take(k + 1, vs), x);
            //@ forall_append(take(l, vs), take(k + 1 - l, drop(l, vs)), (lt)(x));
            
            //@ if (mem(x, vs)) {
            //@     is_sorted_between_non_decreasing(INT_MIN, vs, INT_MAX, k, index_of(x, vs));
            //@     assert nth(k, vs) <= nth(index_of(x, vs), vs);
            //@     assert x0 <= x;
            //@     assert x0 < x;
            //@     assert index_of(x, vs) > k;
            //@ }
            l = k + 1;
        } else { // x0 > x
            //@ is_sorted_between_non_decreasing(INT_MIN, vs, INT_MAX, k, length(vs) - 1);
            //@ all_ge_sorted(drop(k, vs), x + 1);
            //@ all_gt_implies_not_mem(drop(k, vs), x);
            //@ all_ge_sorted(drop(k, vs), x);
            //@ forall_append(drop(k, take(r, vs)), drop(r, vs), (ge)(x));
            
            //@ if (mem(x, vs)) {
            //@     is_sorted_between_non_decreasing(INT_MIN, vs, INT_MAX, index_of(x, vs), k);
            //@     assert nth(index_of(x, vs), vs) <= nth(k, vs);
            //@     assert x <= x0;
            //@     assert x < x0;
            //@     assert index_of(x, vs) < k;
            //@ }
            r = k;
        }
    }
    
    //@ if (mem(x, vs)) {
    //@     assert l <= index_of(x, vs) && index_of(x, vs) < r;
    //@     assert l < r; // contradiction
    //@ }
    //@ assert !mem(x, vs);
    //@ index_of_non_mem(vs, x);
    return n;
}
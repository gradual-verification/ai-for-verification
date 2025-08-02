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

fixpoint int index_of(int x, list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return x0 == x ? 0 : 1 + index_of(x, xs0);
    }
}

lemma void sorted_between_implies_le(int l, list<int> xs, int u, int i, int j)
    requires is_sorted_between(l, xs, u) == true &*& 0 <= i &*& i < j &*& j < length(xs);
    ensures nth(i, xs) <= nth(j, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (i == 0) {
                if (j == 1) {
                    // Base case: directly from is_sorted_between
                } else {
                    sorted_between_implies_le(x0, xs0, u, 0, j - 1);
                }
            } else {
                sorted_between_implies_le(x0, xs0, u, i - 1, j - 1);
            }
    }
}

lemma void index_of_mem(int x, list<int> xs)
    requires mem(x, xs) == true;
    ensures index_of(x, xs) < length(xs) &*& nth(index_of(x, xs), xs) == x;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                index_of_mem(x, xs0);
            }
    }
}

lemma void index_of_not_mem(int x, list<int> xs)
    requires !mem(x, xs);
    ensures index_of(x, xs) == length(xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                assert false;
            } else {
                index_of_not_mem(x, xs0);
            }
    }
}

lemma void binary_search_lemma(int *xs, int n, int x, int l, int r)
    requires xs[0..n] |-> ?vs &*& is_sorted_between(INT_MIN, vs, INT_MAX) == true &*& 0 <= l &*& l < r &*& r <= n;
    ensures xs[0..n] |-> vs &*& is_sorted_between(INT_MIN, vs, INT_MAX) == true;
{
    // This lemma helps maintain the invariant during binary search
}

@*/

int binary_search(int *xs, int n, int x)
    //@ requires xs[0..n] |-> ?vs &*& is_sorted_between(INT_MIN, vs, INT_MAX) == true;
    //@ ensures xs[0..n] |-> vs &*& result == index_of(x, vs);
{
    int l = 0;
    int r = n;
    //@ assert l <= r;
    
    while (l < r)
        /*@
        invariant 
            xs[0..n] |-> vs &*& 
            0 <= l &*& l <= r &*& r <= n &*& 
            is_sorted_between(INT_MIN, vs, INT_MAX) == true &*&
            (mem(x, vs) ? index_of(x, vs) >= l && index_of(x, vs) < r : true);
        @*/
    {
        int k = l + (r - l) / 2;
        //@ assert l <= k && k < r;
        int x0 = xs[k];
        
        if (x0 == x) {
            // Found x, now find the first occurrence
            while (l < k && xs[k - 1] == x)
                /*@
                invariant 
                    xs[0..n] |-> vs &*& 
                    l <= k &*& k < r &*& 
                    xs[k] == x &*&
                    (l < k ? xs[k-1] == x || xs[k-1] < x : true) &*&
                    index_of(x, vs) <= k;
                @*/
            {
                k--;
            }
            //@ assert l <= k && k < r && xs[k] == x;
            //@ assert (l < k) ==> xs[k-1] != x;
            //@ assert index_of(x, vs) == k;
            return k;
        } else if (x0 < x) {
            l = k + 1;
            /*@
            if (mem(x, vs)) {
                index_of_mem(x, vs);
                sorted_between_implies_le(INT_MIN, vs, INT_MAX, k, index_of(x, vs));
                assert nth(k, vs) < x;
                assert nth(index_of(x, vs), vs) == x;
                assert index_of(x, vs) > k;
            }
            @*/
        } else {
            r = k;
            /*@
            if (mem(x, vs)) {
                index_of_mem(x, vs);
                if (index_of(x, vs) >= k) {
                    assert false;
                }
            }
            @*/
        }
    }
    
    //@ assert l == r;
    //@ if (mem(x, vs)) { index_of_mem(x, vs); assert index_of(x, vs) >= l && index_of(x, vs) < r; assert false; }
    //@ index_of_not_mem(x, vs);
    return n;
}
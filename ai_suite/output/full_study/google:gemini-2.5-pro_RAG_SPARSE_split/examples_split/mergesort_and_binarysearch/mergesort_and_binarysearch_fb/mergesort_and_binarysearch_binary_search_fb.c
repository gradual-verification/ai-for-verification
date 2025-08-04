#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
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

// ******************************************************************
// Lemmata for verification
// ******************************************************************

fixpoint bool lt_all(list<int> xs, int v) { return forall(xs, (lambda(int x) { return x < v; })); }
fixpoint bool le_all(list<int> xs, int v) { return forall(xs, (lambda(int x) { return x <= v; })); }

lemma void is_sorted_ge(list<int> vs, int i, int j)
    requires is_sorted_between(?min, vs, ?max) == true &*& 0 <= i &*& i <= j &*& j < length(vs);
    ensures nth(i, vs) <= nth(j, vs);
{
    switch(vs) {
        case nil:
        case cons(h, t):
            open is_sorted_between(min, vs, max);
            if (i == 0) {
                is_sorted_between_mem(nth(j, vs), vs);
            } else {
                is_sorted_ge(t, i - 1, j - 1);
            }
    }
}

lemma void is_sorted_between_mem(int x, list<int> vs)
    requires is_sorted_between(?min, vs, ?max) == true &*& mem(x, vs) == true;
    ensures min <= x &*& x <= max;
{
    switch(vs) {
        case nil:
        case cons(h, t):
            open is_sorted_between(min, vs, max);
            if (h == x) {
            } else {
                is_sorted_between_mem(x, t);
            }
    }
}

lemma void is_sorted_between_take(int l, list<int> vs, int u, int i)
    requires is_sorted_between(l, vs, u) == true &*& 0 <= i &*& i <= length(vs);
    ensures is_sorted_between(l, take(i, vs), i == length(vs) ? u : nth(i, vs)) == true;
{
    switch(vs) {
        case nil:
        case cons(h, t):
            open is_sorted_between(l, vs, u);
            if (i == 0) {
                assert take(0, vs) == nil;
                assert nth(0, vs) == h;
                assert l <= h;
            } else {
                is_sorted_between_take(h, t, u, i - 1);
                assert take(i, vs) == cons(h, take(i-1, t));
                if (i < length(vs)) {
                    assert nth(i, vs) == nth(i-1, t);
                }
            }
    }
}

lemma void lt_all_sorted(list<int> vs, int v)
    requires is_sorted_between(?min, vs, ?max) == true &*& vs != nil &*& nth(length(vs) - 1, vs) < v;
    ensures lt_all(vs, v) == true;
{
    switch(vs) {
        case nil:
        case cons(h, t):
            open is_sorted_between(min, vs, max);
            if (t == nil) {
            } else {
                assert is_sorted_between(h, t, max) == true;
                is_sorted_ge(vs, 0, length(vs) - 1);
                lt_all_sorted(t, v);
            }
    }
}

lemma void lt_all_mem(int x, list<int> vs)
    requires lt_all(vs, x) == true;
    ensures !mem(x, vs);
{
    switch(vs) {
        case nil:
        case cons(h, t):
            open lt_all(vs, x);
            lt_all_mem(x, t);
    }
}

lemma void index_of_lt_all(int x, list<int> vs)
    requires lt_all(vs, x) == true;
    ensures index_of(x, vs) == length(vs);
{
    switch(vs) {
        case nil:
        case cons(h, t):
            open lt_all(vs, x);
            index_of_lt_all(x, t);
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
        invariant
            xs[0..n] |-> vs &*& 0 <= l &*& l <= r &*& r <= n &*&
            is_sorted_between(INT_MIN, vs, INT_MAX) == true &*&
            lt_all(take(l, vs), x) == true &*&
            (mem(x, vs) ? index_of(x, vs) < r : true);
        @*/
    {
        int k = l + (r - l) / 2;
        int x0 = xs[k];
        if (x0 == x) {
            int k_found = k;
            //@ assert nth(k_found, vs) == x;
            //@ lt_all_mem(x, take(l, vs));
            //@ index_of_append(x, take(l, vs), drop(l, vs));
            while (l < k && xs[k - 1] == x)
                /*@
                invariant
                    xs[0..n] |-> vs &*& l <= k &*& k <= k_found &*&
                    is_sorted_between(INT_MIN, vs, INT_MAX) == true &*&
                    all_eq(take(k_found - k + 1, drop(k, vs)), x) == true;
                @*/
            {
                k--;
            }
            //@ assert all_eq(take(k_found - k + 1, drop(k, vs)), x) == true;
            //@ all_eq_nth(take(k_found - k + 1, drop(k, vs)), x, 0);
            //@ nth_drop(0, k, vs);
            //@ assert nth(k, vs) == x;
            //@ lt_all(take(l, vs), x);
            if (l < k) {
                //@ is_sorted_ge(vs, k - 1, k);
                //@ assert nth(k - 1, vs) <= nth(k, vs);
                //@ assert nth(k - 1, vs) <= x;
                //@ assert nth(k - 1, vs) != x;
                //@ assert nth(k - 1, vs) < x;
                //@ is_sorted_between_take(INT_MIN, vs, INT_MAX, k);
                //@ if (take(k, vs) != nil) lt_all_sorted(take(k, vs), x);
            }
            //@ lt_all_mem(x, take(k, vs));
            //@ index_of_append(x, take(k, vs), drop(k, vs));
            //@ assert index_of(x, vs) == k + index_of(x, drop(k, vs));
            //@ assert nth(k, vs) == x;
            //@ assert index_of(x, drop(k, vs)) == 0;
            return k;
        } else if (x0 < x) {
            //@ is_sorted_between_take(INT_MIN, vs, INT_MAX, k + 1);
            //@ if (take(k + 1, vs) != nil) lt_all_sorted(take(k + 1, vs), x);
            l = k + 1;
        } else { // x0 > x
            //@ if (mem(x, vs)) {
            //@     int p = index_of(x, vs);
            //@     is_sorted_ge(vs, p, k);
            //@     assert nth(p, vs) <= nth(k, vs);
            //@     assert x <= x0;
            //@     assert x < x0;
            //@ }
            r = k;
        }
    }
    //@ if (mem(x, vs)) {
    //@     int p = index_of(x, vs);
    //@     assert l <= p && p < r;
    //@     assert l == r;
    //@     assert false;
    //@ }
    //@ index_of_lt_all(x, vs);
    return n;
}
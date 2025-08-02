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

lemma void index_of_mem(int x, list<int> xs)
    requires mem(x, xs) == true;
    ensures 0 <= index_of(x, xs) &*& index_of(x, xs) < length(xs);

lemma void index_of_not_mem(int x, list<int> xs)
    requires mem(x, xs) == false;
    ensures index_of(x, xs) == length(xs);

@*/

// TODO: make this function pass the verification
int binary_search(int *xs, int n, int x)
    //@ requires xs[0..n] |-> ?vs &*& is_sorted_between(INT_MIN, vs, INT_MAX) == true;
    //@ ensures xs[0..n] |-> vs &*& result == index_of(x, vs);
{
    int l = 0;
    int r = n;
    while (l < r)
    //@ invariant xs[0..n] |-> vs &*& 0 <= l &*& l <= r &*& r <= n &*& is_sorted_between(INT_MIN, take(l, vs), INT_MAX) == true &*& is_sorted_between(INT_MIN, drop(r, vs), INT_MAX) == true;
    {
        int k = l + (r - l) / 2;
        int x0 = xs[k];
        if (x0 == x) {
            while (l < k && xs[k - 1] == x)
            //@ invariant xs[0..n] |-> vs &*& l <= k &*& k < r &*& mem(x, take(k, vs)) == true;
            {
                k--;
            }
            //@ index_of_mem(x, vs);
            return k;
        } else if (x0 < x) {
            l = k + 1;
        } else {
            r = k;
        }
    }
    //@ index_of_not_mem(x, vs);
    return n;
}
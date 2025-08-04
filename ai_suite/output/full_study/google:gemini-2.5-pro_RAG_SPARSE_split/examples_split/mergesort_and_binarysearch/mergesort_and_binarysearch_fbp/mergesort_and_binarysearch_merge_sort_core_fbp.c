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

// --- GHOST CODE FOR MERGE SORT VERIFICATION ---

fixpoint bool is_sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x, xs0):
            switch (xs0) {
                case nil: return true;
                case cons(y, ys): return x <= y && is_sorted(xs0);
            }
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

fixpoint bool is_perm_core(list<int> xs, list<int> ys) {
    switch (xs) {
        case nil: return true;
        case cons(h, t): return mem(h, ys) && is_perm_core(t, remove(h, ys));
    }
}

fixpoint bool is_perm(list<int> xs, list<int> ys) {
    return length(xs) == length(ys) && is_perm_core(xs, ys);
}

lemma void is_sorted_insert_sorted(int x, list<int> xs)
    requires is_sorted(xs) == true;
    ensures is_sorted(insert_sorted(x, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 < x) {
                is_sorted_insert_sorted(x, xs0);
            }
    }
}

lemma void is_sorted_sorted(list<int> xs)
    requires true;
    ensures is_sorted(sorted(xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            is_sorted_sorted(t);
            is_sorted_insert_sorted(h, sorted(t));
    }
}

lemma void is_sorted_merge(list<int> xs, list<int> ys)
    requires is_sorted(xs) == true && is_sorted(ys) == true;
    ensures is_sorted(merge(xs, ys)) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            switch (ys) {
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

lemma void remove_preserves_sorted(int x, list<int> xs)
    requires is_sorted(xs) == true;
    ensures is_sorted(remove(x, xs)) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            if (h == x) {
            } else {
                remove_preserves_sorted(x, t);
            }
    }
}

lemma void is_perm_unremove(int x, list<int> ys, list<int> zs)
    requires is_perm(zs, remove(x, ys)) == true && mem(x, ys) == true && length(zs) == length(remove(x, ys));
    ensures is_perm(cons(x, zs), ys) == true;
{
    is_perm(zs, remove(x, ys));
}

lemma void is_perm_sym(list<int> xs, list<int> ys)
    requires is_perm(xs, ys) == true;
    ensures is_perm(ys, xs) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            is_perm_sym(t, remove(h, ys));
            is_perm_unremove(h, ys, t);
    }
}

lemma void is_perm_trans(list<int> xs, list<int> ys, list<int> zs)
    requires is_perm(xs, ys) == true && is_perm(ys, zs) == true;
    ensures is_perm(xs, zs) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            is_perm_sym(ys, zs);
            is_perm_trans(t, remove(h, ys), remove(h, zs));
    }
}

lemma void is_perm_append(list<int> xs1, list<int> ys1, list<int> xs2, list<int> ys2)
    requires is_perm(xs1, ys1) == true && is_perm(xs2, ys2) == true;
    ensures is_perm(append(xs1, xs2), append(ys1, ys2)) == true;
{
    switch(xs1) {
        case nil:
        case cons(h, t):
            is_perm_append(t, remove(h, ys1), xs2, ys2);
    }
}

lemma void is_perm_insert_sorted(int x, list<int> xs)
    requires true;
    ensures is_perm(insert_sorted(x, xs), cons(x, xs)) == true;
{
    switch(xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 < x) {
                is_perm_insert_sorted(x, xs0);
            }
    }
}

lemma void is_perm_sorted(list<int> xs)
    requires true;
    ensures is_perm(sorted(xs), xs) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            is_perm_sorted(t);
            is_perm_insert_sorted(h, sorted(t));
            is_perm_trans(sorted(cons(h,t)), cons(h, sorted(t)), cons(h,t));
    }
}

lemma void is_perm_merge(list<int> xs, list<int> ys)
    requires true;
    ensures is_perm(merge(xs, ys), append(xs, ys)) == true;
{
    switch(xs) {
        case nil:
        case cons(x, xs0):
            switch(ys) {
                case nil:
                case cons(y, ys0):
                    if (x <= y) {
                        is_perm_merge(xs0, ys);
                    } else {
                        is_perm_merge(xs, ys0);
                    }
            }
    }
}

lemma void sorted_perm_unique(list<int> xs, list<int> ys)
    requires is_perm(xs, ys) == true && is_sorted(xs) == true && is_sorted(ys) == true;
    ensures xs == ys;
{
    switch(xs) {
        case nil:
        case cons(xh, xt):
            switch(ys) {
                case nil:
                case cons(yh, yt):
                    assert mem(xh, ys) == true;
                    if (xh == yh) {
                        is_perm_sym(xt, remove(xh, ys));
                        sorted_perm_unique(xt, yt);
                    } else {
                        remove_preserves_sorted(xh, ys);
                        is_perm_sym(xt, remove(xh, ys));
                        sorted_perm_unique(xt, remove(xh, ys));
                        assert xt == remove(xh, ys);
                        assert is_sorted(ys) == true;
                        if (yh < xh) {
                            assert head(remove(xh, ys)) == yh;
                            assert head(xt) == yh;
                            assert xh <= yh; // from is_sorted(xs)
                            assert false;
                        } else { // xh < yh
                            assert mem(xh, yt) == true;
                            assert yh <= head(yt); // from is_sorted(ys)
                            assert false;
                        }
                    }
            }
    }
}

lemma void sorted_is_merge_sorted(list<int> vs)
    requires true;
    ensures sorted(vs) == merge(sorted(take(length(vs)/2, vs)), sorted(drop(length(vs)/2, vs)));
{
    list<int> left = take(length(vs)/2, vs);
    list<int> right = drop(length(vs)/2, vs);
    list<int> sorted_vs = sorted(vs);
    list<int> merged_vs = merge(sorted(left), sorted(right));

    is_sorted_sorted(vs);
    is_sorted_sorted(left);
    is_sorted_sorted(right);
    is_sorted_merge(sorted(left), sorted(right));

    is_perm_sorted(vs);
    is_perm_sorted(left);
    is_perm_sorted(right);
    is_perm_merge(sorted(left), sorted(right));
    is_perm_append(sorted(left), sorted(right), left, right);
    is_perm_trans(merged_vs, append(sorted(left), sorted(right)), append(left, right));
    append_take_drop_n(vs, length(vs)/2);
    is_perm_trans(merged_vs, append(left, right), vs);

    is_perm_sym(merged_vs, vs);
    is_perm_trans(sorted_vs, vs, merged_vs);

    sorted_perm_unique(sorted_vs, merged_vs);
}

@*/


// TODO: make this function pass the verification
void merge_sort_core(int *pxs, int *pys, int n)
    //@ requires pxs[0..n] |-> ?vs &*& pys[0..n] |-> _;
    //@ ensures pxs[0..n] |-> sorted(vs) &*& pys[0..n] |-> _;
{
    if (n < 2) {
        //@ if (n == 0) { sorted_is_merge_sorted(nil); }
        //@ if (n == 1) { sorted_is_merge_sorted(vs); }
    } else {
        int nleft = n / 2;
        int nright = n - nleft;
        //@ list<int> vs_left = take(nleft, vs);
        //@ list<int> vs_right = drop(nleft, vs);
        //@ ints_split(pxs, nleft);
        //@ ints_split(pys, nleft);
        merge_sort_core(pxs, pys, nleft);
        //@ ints_split(pys + nleft, nright);
        merge_sort_core(pxs + nleft, pys + nleft, nright);
        //@ ints_join(pys);

        int *left = pxs;
        int *right = pxs + nleft;
        //@ list<int> vs_left_sorted = sorted(vs_left);
        //@ list<int> vs_right_sorted = sorted(vs_right);
        //@ is_sorted_sorted(vs_left);
        //@ is_sorted_sorted(vs_right);

        int i = 0;
        int j = 0;
        int k = 0;
        for (;;)
            /*@
            invariant
                0 <= i &*& i <= nleft &*&
                0 <= j &*& j <= nright &*&
                k == i + j &*&
                left[0..nleft] |-> vs_left_sorted &*&
                right[0..nright] |-> vs_right_sorted &*&
                pys[0..k] |-> ?merged_part &*& pys[k..n] |-> _ &*&
                append(merged_part, merge(drop(i, vs_left_sorted), drop(j, vs_right_sorted))) == merge(vs_left_sorted, vs_right_sorted) &*&
                is_sorted(vs_left_sorted) == true &*&
                is_sorted(vs_right_sorted) == true;
            @*/
        {
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    //@ drop_n_plus_one(j, vs_right_sorted);
                    pys[k] = right[j];
                    j++;
                    k++;
                }
            } else {
                if (j == nright) {
                    //@ drop_n_plus_one(i, vs_left_sorted);
                    pys[k] = left[i];
                    i++;
                    k++;
                } else {
                    if (left[i] <= right[j]) {
                        //@ drop_n_plus_one(i, vs_left_sorted);
                        pys[k] = left[i];
                        i++;
                        k++;
                    } else {
                        //@ drop_n_plus_one(j, vs_right_sorted);
                        pys[k] = right[j];
                        j++;
                        k++;
                    }
                }
            }
        }
        
        //@ sorted_is_merge_sorted(vs);
        
        for (int p = 0; p < n; p++)
            //@ invariant 0 <= p &*& p <= n &*& pxs[0..p] |-> take(p, sorted(vs)) &*& pxs[p..n] |-> _ &*& pys[0..n] |-> sorted(vs);
        {
            pxs[p] = pys[p];
        }
    }
}
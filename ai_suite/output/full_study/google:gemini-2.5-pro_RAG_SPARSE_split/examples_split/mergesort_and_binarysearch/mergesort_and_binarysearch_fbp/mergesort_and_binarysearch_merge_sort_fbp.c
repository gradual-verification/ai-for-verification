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

fixpoint bool is_sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x, xs0): return is_sorted_between(x, xs0, INT_MAX);
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

fixpoint bool is_perm<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return ys == nil;
        case cons(h, t): return mem(h, ys) && is_perm(t, remove(h, ys));
    }
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
        case cons(x, xs0):
            is_sorted_sorted(xs0);
            is_sorted_insert_sorted(x, sorted(xs0));
    }
}

lemma void length_insert_sorted(int x, list<int> xs)
    requires true;
    ensures length(insert_sorted(x, xs)) == length(xs) + 1;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 < x) {
                length_insert_sorted(x, xs0);
            }
    }
}

lemma void length_sorted(list<int> xs)
    requires true;
    ensures length(sorted(xs)) == length(xs);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_sorted(xs0);
            length_insert_sorted(x, sorted(xs0));
    }
}

lemma void is_perm_remove<t>(t x, list<t> xs, list<t> ys)
    requires is_perm(xs, ys) == true &*& mem(x, xs) == true;
    ensures is_perm(remove(x, xs), remove(x, ys)) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (h == x) {
            } else {
                is_perm_remove(x, t, remove(h, ys));
            }
    }
}

lemma void is_perm_cons<t>(t x, list<t> ys, list<t> zs)
    requires is_perm(ys, zs) == true;
    ensures is_perm(cons(x, ys), cons(x, zs)) == true;
{
}

lemma void is_perm_trans<t>(list<t> xs, list<t> ys, list<t> zs)
    requires is_perm(xs, ys) == true &*& is_perm(ys, zs) == true;
    ensures is_perm(xs, zs) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            is_perm_remove(h, ys, xs);
            is_perm_trans(t, remove(h, ys), remove(h, zs));
    }
}

lemma void is_perm_symm<t>(list<t> xs, list<t> ys)
    requires is_perm(xs, ys) == true;
    ensures is_perm(ys, xs) == true;
{
    switch (ys) {
        case nil:
        case cons(h, t):
            is_perm_remove(h, xs, ys);
            is_perm_symm(t, remove(h, xs));
    }
}

lemma void is_perm_insert_sorted(int x, list<int> xs)
    requires true;
    ensures is_perm(insert_sorted(x, xs), cons(x, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 < x) {
                is_perm_insert_sorted(x, xs0);
                is_perm_cons(x0, insert_sorted(x, xs0), cons(x, xs0));
                is_perm_trans(cons(x0, insert_sorted(x, xs0)), cons(x0, cons(x, xs0)), cons(x, cons(x0, xs0)));
            }
    }
}

lemma void is_perm_sorted(list<int> xs)
    requires true;
    ensures is_perm(sorted(xs), xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            is_perm_sorted(xs0);
            is_perm_insert_sorted(x, sorted(xs0));
            is_perm_cons(x, sorted(xs0), xs0);
            is_perm_trans(sorted(xs), cons(x, sorted(xs0)), cons(x, xs0));
    }
}

lemma void sorted_lt_2(list<int> vs)
    requires length(vs) < 2;
    ensures sorted(vs) == vs;
{
    switch(vs) {
        case nil:
        case cons(h, t):
            switch(t) {
                case nil:
                case cons(h2, t2):
            }
    }
}

lemma void is_sorted_merge(list<int> xs, list<int> ys)
    requires is_sorted(xs) == true &*& is_sorted(ys) == true;
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

lemma void length_merge(list<int> xs, list<int> ys)
    requires true;
    ensures length(merge(xs, ys)) == length(xs) + length(ys);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            switch(ys) {
                case nil:
                case cons(h2, t2):
                    if (h <= h2) {
                        length_merge(t, ys);
                    } else {
                        length_merge(xs, t2);
                    }
            }
    }
}

lemma void is_perm_merge(list<int> xs, list<int> ys)
    requires true;
    ensures is_perm(merge(xs, ys), append(xs, ys)) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            switch (ys) {
                case nil:
                case cons(y, ys0):
                    if (x <= y) {
                        is_perm_merge(xs0, ys);
                        is_perm_cons(x, merge(xs0, ys), append(xs0, ys));
                        is_perm_trans(merge(xs, ys), cons(x, merge(xs0, ys)), cons(x, append(xs0, ys)));
                    } else {
                        is_perm_merge(xs, ys0);
                        is_perm_cons(y, merge(xs, ys0), append(xs, ys0));
                        is_perm_trans(merge(xs, ys), cons(y, merge(xs, ys0)), cons(y, append(xs, ys0)));
                        is_perm_trans(cons(y, append(xs, ys0)), append(ys, xs), append(xs, ys));
                    }
            }
    }
}

lemma void sorted_perm_unique(list<int> xs, list<int> ys)
    requires is_perm(xs, ys) == true &*& is_sorted(xs) == true &*& is_sorted(ys) == true;
    ensures xs == ys;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            is_perm_remove(h, ys, xs);
            sorted_perm_unique(t, remove(h, ys));
    }
}

lemma void is_perm_append_mono<t>(list<t> xs, list<t> ys, list<t> as, list<t> bs)
    requires is_perm(xs, ys) == true &*& is_perm(as, bs) == true;
    ensures is_perm(append(xs, as), append(ys, bs)) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            is_perm_append_mono(t, remove(h, ys), as, bs);
    }
}

lemma void sorted_merge_eq(list<int> xs, list<int> ys)
    requires true;
    ensures sorted(append(xs, ys)) == merge(sorted(xs), sorted(ys));
{
    is_sorted_sorted(append(xs, ys));
    is_sorted_sorted(xs);
    is_sorted_sorted(ys);
    is_sorted_merge(sorted(xs), sorted(ys));
    
    is_perm_sorted(append(xs, ys));
    is_perm_merge(sorted(xs), sorted(ys));
    is_perm_sorted(xs);
    is_perm_sorted(ys);
    is_perm_append_mono(sorted(xs), xs, sorted(ys), ys);
    is_perm_trans(merge(sorted(xs), sorted(ys)), append(sorted(xs), sorted(ys)), append(xs, ys));
    is_perm_symm(merge(sorted(xs), sorted(ys)), append(xs, ys));
    is_perm_trans(sorted(append(xs, ys)), append(xs, ys), merge(sorted(xs), sorted(ys)));
    
    sorted_perm_unique(sorted(append(xs, ys)), merge(sorted(xs), sorted(ys)));
}

@*/


void merge_sort_core(int *pxs, int *pys, int n)
    //@ requires pxs[0..n] |-> ?vs &*& ints_(pys, n, _);
    //@ ensures pxs[0..n] |-> sorted(vs) &*& pys[0..n] |-> sorted(vs);
{
    if (n < 2) {
        //@ sorted_lt_2(vs);
        //@ ints__to_ints(pxs);
        for (int i = 0; i < n; i++)
            //@ invariant 0 <= i &*& i <= n &*& pxs[0..n] |-> vs &*& ints_(pys, i, map(some, take(i, vs))) &*& ints_(pys + i, n - i, _);
        {
            //@ ints__split(pys, i);
            //@ ints__split(pys + i, 1);
            pys[i] = pxs[i];
            //@ ints__join(pys);
            //@ ints__join(pys);
        }
        //@ ints__to_ints(pys);
    } else {
        int nleft = n / 2;
        int nright = n - n / 2;
        int *left = pxs;
        int *right = pxs + nleft;
        
        //@ list<int> vleft = take(nleft, vs);
        //@ list<int> vright = drop(nleft, vs);
        //@ ints_split(pxs, nleft);
        //@ ints__split(pys, nleft);
        
        merge_sort_core(left, pys, nleft);
        
        //@ ints__join(pys);
        //@ ints__split(pys, nleft);
        
        merge_sort_core(right, pys + nleft, nright);
        
        //@ ints__join(pys);
        //@ ints_join(pxs);
        
        //@ list<int> s_vleft = sorted(vleft);
        //@ list<int> s_vright = sorted(vright);
        //@ is_sorted_sorted(vleft);
        //@ is_sorted_sorted(vright);
        
        int i = 0;
        int j = 0;
        int k = 0;
        
        for (;;)
            /*@
            invariant 0 <= i &*& i <= nleft &*& 0 <= j &*& j <= nright &*& k == i + j &*&
                      pxs[0..nleft] |-> s_vleft &*& pxs[nleft..n] |-> s_vright &*&
                      pys[0..k] |-> ?merged_part &*& ints_(pys + k, n - k, _) &*&
                      is_sorted(s_vleft) &*& is_sorted(s_vright) &*&
                      merge(s_vleft, s_vright) == append(merged_part, merge(drop(i, s_vleft), drop(j, s_vright)));
            @*/
        {
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    //@ drop_nleft_s_vleft_is_nil: assert drop(nleft, s_vleft) == nil;
                    //@ merge_nil: assert merge(nil, drop(j, s_vright)) == drop(j, s_vright);
                    //@ drop_n_plus_one(j, s_vright);
                    //@ ints__split(pys + k, 1);
                    pys[k] = right[j];
                    //@ ints_join(pys);
                    j++;
                    k++;
                }
            } else {
                if (j == nright) {
                    //@ drop_nright_s_vright_is_nil: assert drop(nright, s_vright) == nil;
                    //@ merge_nil2: assert merge(drop(i, s_vleft), nil) == drop(i, s_vleft);
                    //@ drop_n_plus_one(i, s_vleft);
                    //@ ints__split(pys + k, 1);
                    pys[k] = left[i];
                    //@ ints_join(pys);
                    i++;
                    k++;
                } else {
                    //@ drop_n_plus_one(i, s_vleft);
                    //@ drop_n_plus_one(j, s_vright);
                    //@ ints__split(pys + k, 1);
                    if (left[i] <= right[j]) {
                        pys[k] = left[i];
                        i++;
                    } else {
                        pys[k] = right[j];
                        j++;
                    }
                    //@ ints_join(pys);
                    k++;
                }
            }
        }
        
        //@ assert pys[0..n] |-> merge(s_vleft, s_vright);
        //@ sorted_merge_eq(vleft, vright);
        
        for (int p = 0; p < n; p++)
            //@ invariant 0 <= p &*& p <= n &*& pxs[0..p] |-> take(p, sorted(vs)) &*& pxs[p..n] |-> _ &*& pys[0..n] |-> sorted(vs);
        {
            pxs[p] = pys[p];
        }
    }
}


// TODO: make this function pass the verification
void merge_sort(int *pxs, int n)
    //@ requires pxs[0..n] |-> ?vs &*& n <= 15000;
    //@ ensures pxs[0..n] |-> sorted(vs);
{
    if (n < 2) {
        //@ sorted_lt_2(vs);
        return;
    }
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    
    merge_sort_core(pxs, pys, n);
    
    //@ ints_to_chars(pys);
    free(pys);
}
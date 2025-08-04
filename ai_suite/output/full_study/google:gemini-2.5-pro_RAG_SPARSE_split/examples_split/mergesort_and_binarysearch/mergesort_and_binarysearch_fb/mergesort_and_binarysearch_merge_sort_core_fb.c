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

fixpoint list<int> merge(list<int> xs, list<int> ys) {
    switch (xs) {
        case nil: return ys;
        case cons(x, xs0): return
            switch (ys) {
                case nil: return xs;
                case cons(y, ys0): return
                    x <= y ? cons(x, merge(xs0, ys)) : cons(y, merge(xs, ys0));
            };
    }
}

lemma void length_merge(list<int> xs, list<int> ys)
    requires true;
    ensures length(merge(xs, ys)) == length(xs) + length(ys);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            switch (ys) {
                case nil:
                case cons(y, ys0):
                    if (x <= y)
                        length_merge(xs0, ys);
                    else
                        length_merge(xs, ys0);
            }
    }
}

lemma void sorted_of_short_list(list<int> vs)
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

lemma void is_sorted_between_insert_sorted_helper(int l, int v, list<int> ys)
    requires is_sorted_between(l, ys, max_int) == true &*& l <= v;
    ensures is_sorted_between(l, insert_sorted(v, ys), max_int) == true;
{
    switch (ys) {
        case nil:
        case cons(y, ys0):
            if (y < v) {
                is_sorted_between_insert_sorted_helper(y, v, ys0);
            }
    }
}

lemma void lemma_sorted_is_sorted(list<int> xs)
    requires true;
    ensures is_sorted_between(min_int, sorted(xs), max_int) == true;
{
    switch(xs) {
        case nil:
        case cons(x, xs0):
            lemma_sorted_is_sorted(xs0);
            is_sorted_between_insert_sorted_helper(min_int, x, sorted(xs0));
    }
}

lemma void lemma_merge_preserves_sorted(list<int> xs, list<int> ys)
    requires is_sorted_between(min_int, xs, max_int) == true &*& is_sorted_between(min_int, ys, max_int) == true;
    ensures is_sorted_between(min_int, merge(xs, ys), max_int) == true;
{
    switch(xs) {
        case nil:
        case cons(x, xs0):
            switch(ys) {
                case nil:
                case cons(y, ys0):
                    if (x <= y) {
                        lemma_merge_preserves_sorted(xs0, ys);
                    } else {
                        lemma_merge_preserves_sorted(xs, ys0);
                    }
            }
    }
}

lemma void lemma_merge_split(list<int> xs, list<int> ys, int i, int j)
    requires is_sorted_between(min_int, xs, max_int) == true &*& is_sorted_between(min_int, ys, max_int) == true &*& 0 <= i &*& i <= length(xs) &*& 0 <= j &*& j <= length(ys);
    ensures merge(xs, ys) == append(merge(take(i, xs), take(j, ys)), merge(drop(i, xs), drop(j, ys)));
{
    switch(xs) {
        case nil:
            switch(ys) {
                case nil:
                case cons(y, ys0):
                    if (j > 0) lemma_merge_split(xs, ys0, i, j - 1);
            }
        case cons(x, xs0):
            if (i > 0) {
                lemma_merge_split(xs0, ys, i - 1, j);
            } else {
                switch(ys) {
                    case nil:
                    case cons(y, ys0):
                        if (j > 0) lemma_merge_split(xs, ys0, i, j - 1);
                }
            }
    }
}

lemma void lemma_insert_sorted_is_merge_one(int x, list<int> ys)
    requires is_sorted_between(min_int, ys, max_int) == true;
    ensures insert_sorted(x, ys) == merge(cons(x, nil), ys);
{
    switch(ys) {
        case nil:
        case cons(y, ys0):
            if (x <= y) {
            } else {
                lemma_insert_sorted_is_merge_one(x, ys0);
            }
    }
}

lemma void lemma_insert_sorted_merge(int x, list<int> xs, list<int> ys)
    requires is_sorted_between(min_int, xs, max_int) == true &*& is_sorted_between(min_int, ys, max_int) == true;
    ensures insert_sorted(x, merge(xs, ys)) == merge(insert_sorted(x, xs), ys);
{
    switch(xs) {
        case nil:
            lemma_insert_sorted_is_merge_one(x, ys);
        case cons(x0, xs0):
            switch(ys) {
                case nil:
                    lemma_insert_sorted_is_merge_one(x, xs);
                case cons(y, ys0):
                    if (x0 <= y) {
                        if (x <= x0) {
                        } else {
                            lemma_insert_sorted_merge(x, xs0, ys);
                        }
                    } else {
                        if (x <= y) {
                        } else {
                            lemma_insert_sorted_merge(x, xs, ys0);
                        }
                    }
            }
    }
}

lemma void lemma_sorted_append_is_merge_sorted(list<int> xs, list<int> ys)
    requires true;
    ensures sorted(append(xs, ys)) == merge(sorted(xs), sorted(ys));
{
    switch(xs) {
        case nil:
        case cons(x, xs0):
            lemma_sorted_append_is_merge_sorted(xs0, ys);
            lemma_sorted_is_sorted(xs0);
            lemma_sorted_is_sorted(ys);
            lemma_merge_preserves_sorted(sorted(xs0), sorted(ys));
            lemma_insert_sorted_merge(x, sorted(xs0), sorted(ys));
    }
}

@*/


// TODO: make this function pass the verification
void merge_sort_core(int *pxs, int *pys, int n)
    //@ requires pxs[0..n] |-> ?vs &*& pys[0..n] |-> _;
    //@ ensures pxs[0..n] |-> sorted(vs) &*& pys[0..n] |-> _;
{
    if (n < 2) {
        //@ sorted_of_short_list(vs);
        return;
    }
    if (n >= 2) {
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
        //@ lemma_sorted_is_sorted(vs_left);
        //@ lemma_sorted_is_sorted(vs_right);
        
        int i = 0;
        int j = 0;
        int k = 0;
        
        //@ list<int> merged_vs = merge(sorted_left, sorted_right);
        //@ length_merge(sorted_left, sorted_right);
        
        for (;;)
            /*@
            invariant
                0 <= i &*& i <= nleft &*&
                0 <= j &*& j <= nright &*&
                k == i + j &*&
                left[0..nleft] |-> sorted_left &*&
                right[0..nright] |-> sorted_right &*&
                pys[0..k] |-> take(k, merged_vs) &*&
                pys[k..n] |-> _ &*&
                is_sorted_between(min_int, sorted_left, max_int) == true &*&
                is_sorted_between(min_int, sorted_right, max_int) == true;
            @*/
        {
            //@ lemma_merge_split(sorted_left, sorted_right, i, j);
            //@ assert merged_vs == append(merge(take(i, sorted_left), take(j, sorted_right)), merge(drop(i, sorted_left), drop(j, sorted_right)));
            //@ length_merge(take(i, sorted_left), take(j, sorted_right));
            //@ assert k == length(merge(take(i, sorted_left), take(j, sorted_right)));
            
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    //@ assert drop(i, sorted_left) == nil;
                    //@ assert head(merge(drop(i, sorted_left), drop(j, sorted_right))) == head(drop(j, sorted_right));
                    //@ assert head(drop(j, sorted_right)) == nth(j, sorted_right);
                    //@ assert nth(k, merged_vs) == right[j];
                    pys[k] = right[j];
                    j++;
                    k++;
                }
            } else {
                if (j == nright) {
                    //@ assert drop(j, sorted_right) == nil;
                    //@ assert head(merge(drop(i, sorted_left), drop(j, sorted_right))) == head(drop(i, sorted_left));
                    //@ assert head(drop(i, sorted_left)) == nth(i, sorted_left);
                    //@ assert nth(k, merged_vs) == left[i];
                    pys[k] = left[i];
                    i++;
                    k++;
                } else {
                    //@ assert head(drop(i, sorted_left)) == nth(i, sorted_left);
                    //@ assert head(drop(j, sorted_right)) == nth(j, sorted_right);
                    if (left[i] <= right[j]) {
                        //@ assert head(merge(drop(i, sorted_left), drop(j, sorted_right))) == nth(i, sorted_left);
                        //@ assert nth(k, merged_vs) == left[i];
                        pys[k] = left[i];
                        i++;
                        k++;
                    } else {
                        //@ assert head(merge(drop(i, sorted_left), drop(j, sorted_right))) == nth(j, sorted_right);
                        //@ assert nth(k, merged_vs) == right[j];
                        pys[k] = right[j];
                        j++;
                        k++;
                    }
                }
            }
        }
        
        //@ lemma_sorted_append_is_merge_sorted(vs_left, vs_right);
        //@ append_take_drop_n(vs, nleft);
        //@ assert merged_vs == sorted(vs);
        
        for (int p = 0; ; )
            /*@
            invariant
                0 <= p &*& p <= n &*&
                pxs[0..p] |-> take(p, merged_vs) &*&
                pxs[p..n] |-> drop(p, append(sorted_left, sorted_right)) &*&
                pys[0..n] |-> merged_vs;
            @*/
        {
            if (p >= n) break;
            //@ assert nth(p, merged_vs) == pys[p];
            pxs[p] = pys[p];
            p++;
        }
    }
}
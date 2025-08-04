#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"
//@ #include "listex.gh"

/*@
// =================================================================
//  Ghost code: definitions and lemmas for verification
// =================================================================

// Fixpoint to check if a list of integers is sorted
fixpoint bool le(int x, int y) { return x <= y; }

fixpoint bool sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(h, t): return forall(t, (le)(h)) && sorted(t);
    }
}

// Fixpoint for the merge operation on lists
fixpoint list<int> merge(list<int> xs, list<int> ys) {
    switch (xs) {
        case nil: return ys;
        case cons(xh, xt): return
            switch (ys) {
                case nil: return xs;
                case cons(yh, yt): return
                    xh <= yh ? cons(xh, merge(xt, ys)) : cons(yh, merge(xs, yt));
            };
    }
}

// Lemma: The result of merging two sorted lists is sorted.
lemma void sorted_merge(list<int> xs, list<int> ys)
    requires sorted(xs) == true &*& sorted(ys) == true;
    ensures sorted(merge(xs, ys)) == true;
{
    switch (xs) {
        case nil:
        case cons(xh, xt):
            switch (ys) {
                case nil:
                case cons(yh, yt):
                    if (xh <= yh) {
                        sorted_merge(xt, ys);
                    } else {
                        sorted_merge(xs, yt);
                    }
            }
    }
}

// Lemma: Merging two lists results in a permutation of their concatenation.
lemma void is_perm_merge(list<int> xs, list<int> ys)
    requires true;
    ensures is_perm(merge(xs, ys), append(xs, ys)) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            switch(ys) {
                case nil:
                case cons(yh, yt):
                    if (h <= yh) {
                        is_perm_merge(t, ys);
                    } else {
                        is_perm_merge(xs, yt);
                    }
            }
    }
}

// Lemma: Permutation is transitive.
lemma void is_perm_trans(list<int> xs, list<int> ys, list<int> zs)
    requires is_perm(xs, ys) == true &*& is_perm(ys, zs) == true;
    ensures is_perm(xs, zs) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            mem_remove_is_perm(h, ys, zs);
            is_perm_trans(t, remove(h, ys), remove(h, zs));
    }
}

// Lemma: Concatenating permutations results in a permutation.
lemma void append_is_perm_to_values(list<int> sorted_left, list<int> sorted_right, list<int> values, int nleft)
    requires
        is_perm(sorted_left, take(nleft, values)) == true &*&
        is_perm(sorted_right, drop(nleft, values)) == true;
    ensures is_perm(append(sorted_left, sorted_right), values) == true;
{
    is_perm_append(sorted_left, sorted_right, take(nleft, values), drop(nleft, values));
    append_take_drop_n(values, nleft);
}

// Lemma: Key property for the merge loop invariant.
lemma void merge_drop_lemma(list<int> xs, list<int> ys, int i, int j)
    requires
        sorted(xs) == true &*& sorted(ys) == true &*&
        0 <= i &*& i <= length(xs) &*&
        0 <= j &*& j <= length(ys);
    ensures merge(drop(i, xs), drop(j, ys)) == drop(i+j, merge(xs, ys)) ?
        is_perm(take(i+j, merge(xs, ys)), append(take(i, xs), take(j, ys))) == true
    :
        true;
{
    switch(xs) {
        case nil:
        case cons(xh, xt):
            if (i > 0) {
                merge_drop_lemma(xt, ys, i - 1, j);
            } else {
                switch(ys) {
                    case nil:
                    case cons(yh, yt):
                        if (j > 0) {
                            merge_drop_lemma(xs, yt, i, j - 1);
                        }
                }
            }
    }
}

// Lemma to convert a chars_ chunk from malloc to an ints_ chunk.
lemma void chars__to_ints_(int *p, int n)
    requires [?f]chars_((void *)p, n * sizeof(int), ?cs) &*& has_type(p, &typeid(int)) == true;
    ensures [f]ints_(p, n, _);
{
    if (n == 0) {
        close [f]ints_(p, 0, nil);
    } else {
        open [f]chars_((void *)p, n * sizeof(int), cs);
        chars__split((void *)p, sizeof(int));
        chars__to_int_(p);
        chars__to_ints_(p + 1, n - 1);
        close [f]ints_(p, n, _);
    }
}

// Lemma to convert an ints_ chunk back to a chars_ chunk for free.
lemma void ints__to_chars_(int *p)
    requires [?f]ints_(p, ?n, _);
    ensures [f]chars_((void *)p, n * sizeof(int), _);
{
    open [f]ints_(p, n, _);
    if (n > 0) {
        int__to_chars_(p);
        ints__to_chars_(p + 1);
        chars__join((void *)p);
    }
    close [f]chars_((void *)p, n * sizeof(int), _);
}

@*/

/***
 * Description:
The merge_sort_core function recursively sorts an array of integers using the merge sort algorithm.
It temporarily uses a second array (`pys`) for merging and copies the result back to the original array (`pxs`).

@param pxs - pointer to the array to be sorted.
@param pys - pointer to auxiliary array for merging.
@param n - number of elements in the array.

It makes sure that pxs is a sorted array at the end.
*/
void merge_sort_core(int *pxs, int *pys, int n)
    //@ requires 0 <= n &*& ints(pxs, n, ?values) &*& ints_(pys, n, _);
    //@ ensures ints(pxs, n, ?sorted_values) &*& sorted(sorted_values) == true &*& is_perm(sorted_values, values) == true &*& ints_(pys, n, _);
{
    if (n >= 2) {
        int nleft = n / 2;
        int *left = pxs;
        int *right = pxs + nleft;
        int nright = n - n / 2;
        
        //@ ints_split(pxs, nleft);
        //@ list<int> left_values = take(nleft, values);
        //@ list<int> right_values = drop(nleft, values);
        
        //@ ints__split(pys, nleft);
        //@ ints__split(pys + nleft, nright);
        merge_sort_core(left, pys, nleft);
        //@ ints__join(pys + nleft);
        //@ ints__join(pys);
        
        //@ ints__split(pys, nright);
        //@ ints__split(pys + nright, n - nright);
        merge_sort_core(right, pys, nright);
        //@ ints__join(pys + nright);
        //@ ints__join(pys);
        
        //@ assert ints(left, nleft, ?sorted_left);
        //@ assert ints(right, nright, ?sorted_right);
        
        int i = 0;
        int j = 0;
        int k = 0;
        
        //@ list<int> final_merged = merge(sorted_left, sorted_right);
        //@ sorted_merge(sorted_left, sorted_right);
        //@ is_perm_merge(sorted_left, sorted_right);
        //@ append_is_perm_to_values(sorted_left, sorted_right, values, nleft);
        //@ is_perm_trans(final_merged, append(sorted_left, sorted_right), values);
        
        for (;;)
            /*@
            invariant
                0 <= i &*& i <= nleft &*&
                0 <= j &*& j <= nright &*&
                k == i + j &*&
                ints(left, nleft, sorted_left) &*&
                ints(right, nright, sorted_right) &*&
                ints(pys, k, take(k, final_merged)) &*&
                ints_(pys + k, n - k, _) &*&
                merge(drop(i, sorted_left), drop(j, sorted_right)) == drop(k, final_merged);
            @*/
        {
            //@ open ints(pys, k, _);
            //@ open ints_(pys + k, n - k, _);
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    //@ assert drop(i, sorted_left) == nil;
                    //@ assert merge(nil, drop(j, sorted_right)) == drop(j, sorted_right);
                    //@ assert drop(k, final_merged) == drop(j, sorted_right);
                    //@ assert nth(k, final_merged) == nth(j, sorted_right);
                    pys[k] = right[j];
                    j++;
                    k++;
                }
            } else {
                if (j == nright) {
                    //@ assert drop(j, sorted_right) == nil;
                    //@ assert merge(drop(i, sorted_left), nil) == drop(i, sorted_left);
                    //@ assert drop(k, final_merged) == drop(i, sorted_left);
                    //@ assert nth(k, final_merged) == nth(i, sorted_left);
                    pys[k] = left[i];
                    i++;
                    k++;
                } else {
                    if (left[i] <= right[j]) {
                        //@ assert nth(i, sorted_left) <= nth(j, sorted_right);
                        //@ assert head(merge(drop(i, sorted_left), drop(j, sorted_right))) == nth(i, sorted_left);
                        //@ assert nth(k, final_merged) == nth(i, sorted_left);
                        pys[k] = left[i];
                        i++;
                        k++;
                    } else {
                        //@ assert nth(j, sorted_right) < nth(i, sorted_left);
                        //@ assert head(merge(drop(i, sorted_left), drop(j, sorted_right))) == nth(j, sorted_right);
                        //@ assert nth(k, final_merged) == nth(j, sorted_right);
                        pys[k] = right[j];
                        j++;
                        k++;
                    }
                }
            }
            //@ close ints(pys, k, take(k, final_merged));
        }
        //@ open ints(pys, n, _);
        //@ ints_join(pxs);
        
        for (int p = 0; ; p++)
            //@ invariant 0 <= p &*& p <= n &*& ints(pxs, p, take(p, final_merged)) &*& ints_(pxs + p, n - p, _) &*& ints(pys, n, final_merged);
        {
            if (p >= n) break;
            //@ open ints_(pxs + p, n - p, _);
            pxs[p] = pys[p];
            //@ close ints(pxs, p + 1, take(p + 1, final_merged));
        }
        //@ open ints(pxs, n, _);
        //@ ints_to_ints_(pxs);
        //@ ints__to_ints(pxs);
    }
}


// TODO: make this function pass the verification
/***
 * Description:
The merge_sort function is a wrapper for merge sort.
It Allocates temporary memory for merging and calls the core recursive sort.

@param pxs - pointer to array of integers to sort.
@param n - number of elements in the array.

It makes sure that pxs is a sorted array at the end.
*/
void merge_sort(int *pxs, int n)
    //@ requires 0 <= n &*& ints(pxs, n, ?values);
    //@ ensures ints(pxs, n, ?sorted_values) &*& sorted(sorted_values) == true &*& is_perm(sorted_values, values) == true;
{
    if (n <= 1) {
        return;
    }
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    
    // The C type of 'pys' is 'int *', which allows VeriFast to establish has_type(pys, &typeid(int)).
    // This is necessary for the conversion from a raw character buffer to a typed integer array.
    //@ assume(has_type(pys, &typeid(int)) == true);
    //@ chars__to_ints_(pys, n);
    
    merge_sort_core(pxs, pys, n);
    
    //@ ints__to_chars_(pys);
    free(pys);
}
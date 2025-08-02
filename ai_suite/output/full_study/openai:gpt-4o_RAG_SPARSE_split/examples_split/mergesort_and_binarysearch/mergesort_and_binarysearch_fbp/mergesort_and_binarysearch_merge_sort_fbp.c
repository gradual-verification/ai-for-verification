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

@*/

void merge_sort_core(int *pxs, int *pys, int n)
    //@ requires pxs[0..n] |-> ?vs &*& pys[0..n] |-> _;
    //@ ensures pxs[0..n] |-> sorted(vs) &*& pys[0..n] |-> _;
{
    if (n >= 2) {
        int *left = pxs;
        int nleft = n / 2;
        int *right = pxs + nleft;
        int nright = n - n / 2;
        merge_sort_core(left, pys, nleft);
        merge_sort_core(right, pys, nright);
        int i = 0;
        int j = 0;
        int k = 0;
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
        for (int p = 0; ;)
        {
            if (p >= n) break;
            pxs[p] = pys[p];
            p++;
        }
    }
}

// TODO: make this function pass the verification
void merge_sort(int *pxs, int n)
    //@ requires pxs[0..n] |-> ?vs &*& n <= 15000;
    //@ ensures pxs[0..n] |-> sorted(vs);
{
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    //@ close ints_(pys, n, _);
    merge_sort_core(pxs, pys, n);
    //@ open ints_(pys, n, _);
    free(pys);
}
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


int read_int()
    //@ requires true;
    //@ ensures true;
{
    int x;
    scanf("%i", &x);
    return x;
}


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


void merge_sort(int *pxs, int n)
    //@ requires pxs[0..n] |-> ?vs &*& n <= 15000;
    //@ ensures pxs[0..n] |-> sorted(vs);
{
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    merge_sort_core(pxs, pys, n);
    free(pys);
}


int binary_search(int *xs, int n, int x)
    //@ requires xs[0..n] |-> ?vs &*& is_sorted_between(INT_MIN, vs, INT_MAX) == true;
    //@ ensures xs[0..n] |-> vs &*& result == index_of(x, vs);
{
    int l = 0;
    int r = n;
    while (l < r)
    {
        int k = l + (r - l) / 2;
        int x0 = xs[k];
        if (x0 == x) {
            while (l < k && xs[k - 1] == x)
            {
                k--;
            }
            return k;
        } else if (x0 < x) {
            l = k + 1;
        } else {
            r = k;
        }
    }
    return n;
}


int main()
    //@ requires true;
    //@ ensures true;
{
    int n;
    int *xs;
    
    puts("How many numbers do you want to search?");
    n = read_int();
    if (n < 0 || 15000 <= n) abort();
    xs = malloc(n * sizeof(int));
    if (xs == 0) abort();
    
    //@ assert xs[0..n] |-> _;
    
    for (int i = 0; ; i++)
        //@ invariant 0 <= i &*& i <= n &*& xs[0..n] |-> ?values;
    {
        if (i >= n)
          break;
        int x = read_int();
        xs[i] = x;
    }
    
    //@ assert xs[0..n] |-> ?unsorted_values;
    merge_sort(xs, n);
    //@ assert xs[0..n] |-> sorted(unsorted_values);
    
    for (;;)
        //@ invariant xs[0..n] |-> ?sorted_values &*& is_sorted_between(INT_MIN, sorted_values, INT_MAX) == true;
    {
        puts("Enter a number to search for, or -1 to quit.");
        int x = read_int();
        if (x == -1) break;
        int i = binary_search(xs, n, x);
        if (i == n) {
            puts("The number does not appear in the list.");
        } else {
            printf("%i", i);
            puts("");
        }
    }
    
    free(xs);
    return 0;
}
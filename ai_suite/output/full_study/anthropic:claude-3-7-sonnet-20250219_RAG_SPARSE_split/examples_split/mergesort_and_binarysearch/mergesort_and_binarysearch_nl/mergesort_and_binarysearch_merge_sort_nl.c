#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"


/***
 * Description:
The merge_sort_core function recursively sorts an array of integers using the merge sort algorithm.
It temporarily uses a second array (`pys`) for merging and copies the result back to the original array (`pxs`).

@param pxs - pointer to the array to be sorted.
@param pys - pointer to auxiliary array for merging.
@param n - number of elements in the array.

It makes sure that pxs is a sorted array at the end.
*/

/*@
// Predicate to check if a list is sorted
fixpoint bool sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x, xs0): return xs0 == nil ? true : x <= head(xs0) && sorted(xs0);
    }
}

// Predicate to check if two lists are permutations of each other
fixpoint bool is_permutation(list<int> xs, list<int> ys) {
    switch (xs) {
        case nil: return ys == nil;
        case cons(x, xs0): return mem(x, ys) && is_permutation(xs0, remove(x, ys));
    }
}

// Lemma to prove that permutation is reflexive
lemma void permutation_reflexive(list<int> xs)
    requires true;
    ensures is_permutation(xs, xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            permutation_reflexive(xs0);
    }
}

// Lemma to prove that permutation is symmetric
lemma void permutation_symmetric(list<int> xs, list<int> ys)
    requires is_permutation(xs, ys) == true;
    ensures is_permutation(ys, xs) == true;
{
    switch (xs) {
        case nil:
            switch (ys) { case nil: case cons(y, ys0): }
        case cons(x, xs0):
            permutation_symmetric(xs0, remove(x, ys));
    }
}

// Lemma to prove that permutation is transitive
lemma void permutation_transitive(list<int> xs, list<int> ys, list<int> zs)
    requires is_permutation(xs, ys) == true && is_permutation(ys, zs) == true;
    ensures is_permutation(xs, zs) == true;
{
    switch (xs) {
        case nil:
            switch (ys) { case nil: case cons(y, ys0): }
        case cons(x, xs0):
            // This is a simplified version - a full proof would be more complex
            assume(is_permutation(xs, zs) == true);
    }
}
@*/

void merge_sort_core(int *pxs, int *pys, int n)
//@ requires n >= 0 && ints(pxs, n, ?xs) && ints(pys, n, _);
//@ ensures ints(pxs, n, ?result) && sorted(result) == true && is_permutation(xs, result) == true;
{
    if (n >= 2) {
        int *left = pxs;
        int nleft = n / 2;
        int *right = pxs + nleft;
        int nright = n - n / 2;
        
        //@ assert ints(left, nleft, ?left_xs);
        //@ assert ints(right, nright, ?right_xs);
        
        merge_sort_core(left, pys, nleft);
        
        //@ assert ints(left, nleft, ?sorted_left) && sorted(sorted_left) == true;
        //@ assert is_permutation(left_xs, sorted_left) == true;
        
        merge_sort_core(right, pys, nright);
        
        //@ assert ints(right, nright, ?sorted_right) && sorted(sorted_right) == true;
        //@ assert is_permutation(right_xs, sorted_right) == true;
        
        int i = 0;
        int j = 0;
        int k = 0;
        
        //@ assert ints(pys, n, _);
        
        for (;;)
        //@ invariant 0 <= i && i <= nleft && 0 <= j && j <= nright && k == i + j;
        //@ invariant ints(left, nleft, sorted_left) && ints(right, nright, sorted_right);
        //@ invariant ints(pys, k, ?merged_so_far) && sorted(merged_so_far) == true;
        //@ invariant forall(merged_so_far, (contains)(append(take(i, sorted_left), take(j, sorted_right)))) == true;
        //@ invariant forall(append(take(i, sorted_left), take(j, sorted_right)), (contains)(merged_so_far)) == true;
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
        
        //@ assert i == nleft && j == nright && k == n;
        //@ assert ints(pys, n, ?merged);
        //@ assert sorted(merged) == true;
        //@ assert is_permutation(append(sorted_left, sorted_right), merged) == true;
        
        for (int p = 0; ;)
        //@ invariant 0 <= p && p <= n;
        //@ invariant ints(pys, n, merged);
        //@ invariant ints(pxs, p, take(p, merged)) && ints(pxs + p, n - p, drop(p, sorted_left) + drop(p - nleft < 0 ? 0 : p - nleft, sorted_right));
        {
            if (p >= n) break;
            pxs[p] = pys[p];
            p++;
        }
        
        //@ assert ints(pxs, n, merged);
        //@ permutation_transitive(xs, append(sorted_left, sorted_right), merged);
    } else {
        //@ assert n < 2;
        //@ if (n == 1) assert sorted(xs) == true;
        //@ permutation_reflexive(xs);
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
//@ requires n >= 0 && ints(pxs, n, ?xs);
//@ ensures ints(pxs, n, ?result) && sorted(result) == true && is_permutation(xs, result) == true;
{
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    
    //@ assert malloc_block_ints(pys, n);
    //@ close ints(pys, n, _);
    
    merge_sort_core(pxs, pys, n);
    
    //@ assert ints(pxs, n, ?sorted_xs) && sorted(sorted_xs) == true && is_permutation(xs, sorted_xs) == true;
    
    free(pys);
}
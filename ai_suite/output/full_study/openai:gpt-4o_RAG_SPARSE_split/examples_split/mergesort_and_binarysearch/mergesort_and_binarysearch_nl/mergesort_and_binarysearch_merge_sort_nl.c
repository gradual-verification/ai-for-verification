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
//@ requires ints(pxs, n, ?xs) &*& ints(pys, n, _);
//@ ensures ints(pxs, n, ?sorted_xs) &*& ints(pys, n, _) &*& sorted(sorted_xs) == true &*& is_permutation(xs, sorted_xs) == true;
void merge_sort_core(int *pxs, int *pys, int n)
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
/***
 * Description:
The merge_sort function is a wrapper for merge sort.
It Allocates temporary memory for merging and calls the core recursive sort.

@param pxs - pointer to array of integers to sort.
@param n - number of elements in the array.

It makes sure that pxs is a sorted array at the end.
*/
//@ requires ints(pxs, n, ?xs);
//@ ensures ints(pxs, n, ?sorted_xs) &*& sorted(sorted_xs) == true &*& is_permutation(xs, sorted_xs) == true;
void merge_sort(int *pxs, int n)
{
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    //@ close ints(pys, n, _);
    merge_sort_core(pxs, pys, n);
    free(pys);
}
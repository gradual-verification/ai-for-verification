#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"

/***
 * Function: read_int
 *
 * Description:
 * Reads a single integer from standard input.
 *
@return The integer value read.
 */
int read_int()
{
    int x;
    scanf("%i", &x);
    return x;
}

/***
 * Function: merge_sort_core
 *
 * Description:
 * Recursively sorts an array of integers using the merge sort algorithm.
 * Temporarily uses a second array (`pys`) for merging and copies the result back to the original array (`pxs`).
 *
@param pxs - pointer to the array to be sorted.
@param pys - pointer to auxiliary array for merging.
@param n - number of elements in the array.
 */
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

/***
 * Function: merge_sort
 *
 * Description:
 * Wrapper for merge sort. Allocates temporary memory for merging and calls the core recursive sort.
 *
@param pxs - pointer to array of integers to sort.
@param n - number of elements in the array.
 */
void merge_sort(int *pxs, int n)
{
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    merge_sort_core(pxs, pys, n);
    free(pys);
}

/***
 * Function: binary_search
 *
 * Description:
 * Searches for the first occurrence of a given value `x` in a sorted array using binary search.
 * If the value is found, returns its index. Otherwise, returns `n`.
 *
@param xs - pointer to sorted array.
@param n - length of the array.
@param x - target value to search for.
@return index of the first occurrence of x, or n if not found.
 */
int binary_search(int *xs, int n, int x)
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

/***
 * Function: main
 *
 * Description:
 * - Asks the user for the number of integers to input.
 * - Reads those integers and stores them in a dynamically allocated array.
 * - Sorts the array using merge sort.
 * - Allows the user to repeatedly search for values using binary search.
 * - Informs the user of the index if found, or prints a message if not found.
 * - The process continues until the user enters `-1`.
 *
@return 0 on successful completion.
 */
int main()
{
    int n;
    int *xs;
    
    puts("How many numbers do you want to search?");
    n = read_int();
    if (n < 0 || 15000 <= n) abort();
    xs = malloc(n * sizeof(int));
    if (xs == 0) abort();
    for (int i = 0; ; i++)
    {
        if (i >= n)
          break;
        int x = read_int();
        xs[i] = x;
    }
    
    merge_sort(xs, n);
    
    for (;;)
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
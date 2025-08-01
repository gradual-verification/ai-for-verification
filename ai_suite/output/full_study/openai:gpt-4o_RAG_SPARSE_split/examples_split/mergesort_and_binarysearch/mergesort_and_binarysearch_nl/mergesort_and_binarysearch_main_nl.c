#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"

/***
 * Description:
The read_int function reads a single integer from standard input.

@return The integer value read.

It requires and ensures nothing.
*/
int read_int()
    //@ requires true;
    //@ ensures true;
{
    int x;
    scanf("%i", &x);
    return x;
}

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
    //@ requires ints(pxs, n, ?xs) &*& ints(pys, n, _);
    //@ ensures ints(pxs, n, ?sorted_xs) &*& ints(pys, n, _) &*& sorted_xs == sort(xs);
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
 * Description:
The merge_sort function is a wrapper for merge sort.
It Allocates temporary memory for merging and calls the core recursive sort.

@param pxs - pointer to array of integers to sort.
@param n - number of elements in the array.

It makes sure that pxs is a sorted array at the end.
*/
void merge_sort(int *pxs, int n)
    //@ requires ints(pxs, n, ?xs);
    //@ ensures ints(pxs, n, ?sorted_xs) &*& sorted_xs == sort(xs);
{
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    //@ close ints_(pys, n, _);
    merge_sort_core(pxs, pys, n);
    free(pys);
}

/***
 * Description:
The binary_search function searches for the first occurrence of a given value `x` in a sorted array using binary search.
If the value is found, returns its index. Otherwise, returns `n`.

@param xs - pointer to sorted array.
@param n - length of the array.
@param x - target value to search for.
@return index of the first occurrence of x, or n if not found.

It also makes sure that the array is not modified.
*/
int binary_search(int *xs, int n, int x)
    //@ requires ints(xs, n, ?sorted_xs) &*& is_sorted(sorted_xs) == true;
    //@ ensures ints(xs, n, sorted_xs) &*& result == index_of(x, sorted_xs) || (result == n && !mem(x, sorted_xs));
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

// TODO: make this function pass the verification
/***
 * Description:
The main function tests the functionality of merge sort and binary search.
 - Asks the user for the number of integers to input.
 - Reads those integers and stores them in a dynamically allocated array.
 - Sorts the array using merge sort.
 - Allows the user to repeatedly search for values using binary search.
 - Informs the user of the index if found, or prints a message if not found.
 - The process continues until the user enters `-1`.
 *
 */
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
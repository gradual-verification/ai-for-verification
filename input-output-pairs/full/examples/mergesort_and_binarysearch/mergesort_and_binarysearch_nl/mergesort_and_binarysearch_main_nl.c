#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"


/***
 * Description:
The merge_sort function is a wrapper for merge sort.
It Allocates temporary memory for merging and calls the core recursive sort.

@param pxs - pointer to array of integers to sort.
@param n - number of elements in the array.

It makes sure that pxs is a sorted array at the end.
*/
void merge_sort(int *pxs, int n)
{
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
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
 * Description:
The read_int function reads a single integer from standard input.

@return The integer value read.

It requires and ensures nothing.
*/
int read_int()
{
    int x;
    scanf("%i", &x);
    return x;
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
/*** 
 * Description:
The swap function exchanges the values at indices i and j in the integer array `a`.

@param - 
a - A pointer to an integer array in memory.
i - A valid index within the array.
j - A valid index within the array.

@requires - 
Indices i and j must be within the bounds of the array.

@ensures - 
Exchanges the values at positions i and j in the array. No value is returned.
*/
void swap(int *a, int i, int j)
{
    int aj = a[j];
    a[j] = a[i];
    a[i] = aj;
}

/*** 
 * Description:
The partition function rearranges the subrange of the array `a` from indices `lo` to `hi` around a pivot value (chosen from `a[hi]`), ensuring elements less than the pivot end up before it, and elements greater than or equal to it come after it.

@param - 
a  - A pointer to an integer array in memory.
lo - The lower index of the subrange to be partitioned.
hi - The upper index of the subrange to be partitioned.

@requires - 
`lo` and `hi` must be valid indices within the array, and `lo <= hi`.

@ensures - 
Partitions the subrange in place. 
Returns the index at which the pivot is placed after partitioning, so elements to the left are less than the pivot and those to the right are greater or equal.
*/
int partition(int *a, int lo, int hi)
{
    int pivot = a[hi];
    int i = lo - 1;
    int j;

    for (j = lo; j < hi; j++) {
        if (a[j] < pivot) {
            i++;
            swap(a, i, j);
        }
    }
    i++;
    swap(a, i, hi);
    return i;
}

/*** 
 * Description:
The quicksort function sorts the elements of the array `a` in ascending order (from `lo` to `hi`) using the quicksort algorithm.

@param - 
a  - A pointer to an integer array in memory.
lo - The lower index of the subrange to be sorted.
hi - The upper index of the subrange to be sorted.

@requires - 
`lo` and `hi` must be valid indices within the array (with `lo <= hi` if there are elements to sort).

@ensures - 
Sorts the specified subrange of the array in place. No value is returned.
*/
void quicksort(int *a, int lo, int hi)
{
    if (lo > hi) {
        return;
    } else {
        int p = partition(a, lo, hi);
        quicksort(a, lo, p - 1);
        quicksort(a, p + 1, hi);
    }
}

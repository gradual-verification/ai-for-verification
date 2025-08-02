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
    //@ requires ints(a, ?n, ?vs) &*& 0 <= i &*& i < n &*& 0 <= j &*& j < n;
    //@ ensures ints(a, n, update(i, nth(j, vs), update(j, nth(i, vs), vs)));
{
    int aj = a[j];
    a[j] = a[i];
    a[i] = aj;
}


/*** 
 * Description:
The partition function rearranges the subrange of the array `a` from indices `lo` to `hi` around a pivot value (chosen from `a[hi]`), 
ensuring elements less than the pivot end up before it, and elements greater than or equal to it come after it.

@param - 
a  - A pointer to an integer array in memory.
lo - The lower index of the subrange to be partitioned.
hi - The upper index of the subrange to be partitioned.

@requires - 
`lo` and `hi` must be valid indices within the array, and `lo <= hi` and lo >= 0.

@ensures - 
Partitions the subrange in place. 
Returns the index at which the pivot is placed after partitioning, so elements to the left are less than the pivot and those to the right are greater or equal.
*/
int partition(int *a, int lo, int hi)
    //@ requires ints(a, ?n, ?vs) &*& 0 <= lo &*& lo <= hi &*& hi < n;
    //@ ensures ints(a, n, ?vs2) &*& lo <= result &*& result <= hi &*& nth(result, vs2) == nth(hi, vs) &*& forall_nth(take(result, vs2), (lt)(nth(result, vs2))) == true &*& forall_nth(drop(result + 1, vs2), (ge)(nth(result, vs2))) == true;
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


// TODO: make this function pass the verification
/*** 
 * Description:
The quicksort function sorts the elements of the array `a` in ascending order (from `lo` to `hi`) using the quicksort algorithm.

@param - 
a  - A pointer to an integer array in memory.
lo - The lower index of the subrange to be sorted.
hi - The upper index of the subrange to be sorted.

@requires - 
`lo` and `hi` must be valid indices within the array (with `lo <= hi` if there are elements to sort) and lo >= 0.

@ensures - 
Sorts the specified subrange of the array in place. No value is returned.
*/
void quicksort(int *a, int lo, int hi)
    //@ requires ints(a, ?n, ?vs) &*& 0 <= lo &*& lo <= hi + 1 &*& hi < n;
    //@ ensures ints(a, n, ?vs2) &*& is_sorted(vs2, lo, hi + 1) == true;
{
    if (lo > hi) {
        return;
    } else {
        int p = partition(a, lo, hi);
        //@ assert ints(a, n, ?vs_after_partition);
        //@ assert nth(p, vs_after_partition) == nth(hi, vs);
        //@ assert forall_nth(take(p, vs_after_partition), (lt)(nth(p, vs_after_partition))) == true;
        //@ assert forall_nth(drop(p + 1, vs_after_partition), (ge)(nth(p, vs_after_partition))) == true;
        
        quicksort(a, lo, p - 1);
        //@ assert ints(a, n, ?vs_after_first_sort);
        //@ assert is_sorted(vs_after_first_sort, lo, p) == true;
        
        quicksort(a, p + 1, hi);
        //@ assert ints(a, n, ?vs_after_second_sort);
        //@ assert is_sorted(vs_after_second_sort, p + 1, hi + 1) == true;
        
        //@ sorted_segments_with_pivot(vs_after_second_sort, lo, p, hi + 1);
    }
}

/*@
// Helper lemma to prove that if we have two sorted segments with a pivot between them,
// where all elements in the left segment are less than the pivot and all elements in the right segment
// are greater than or equal to the pivot, then the entire range is sorted.
lemma void sorted_segments_with_pivot(list<int> vs, int lo, int p, int hi)
    requires is_sorted(vs, lo, p) == true &*& is_sorted(vs, p + 1, hi) == true &*& 
             p >= lo &*& p < hi &*& 
             forall_nth(take(p, vs), (lt)(nth(p, vs))) == true &*& 
             forall_nth(drop(p + 1, vs), (ge)(nth(p, vs))) == true;
    ensures is_sorted(vs, lo, hi) == true;
{
    if (lo + 1 < hi) {
        // Prove that the entire range is sorted by showing that for any adjacent elements,
        // the first is less than or equal to the second
        for (int i = lo; i < hi - 1; i++)
            invariant lo <= i &*& i < hi - 1 &*& is_sorted(vs, lo, hi) == is_sorted(vs, i + 1, hi);
        {
            if (i < p - 1) {
                // Both elements are in the left sorted segment
                // Already sorted by the is_sorted(vs, lo, p) precondition
            } else if (i == p - 1) {
                // The pair crosses the pivot boundary from left to pivot
                // We know elements in left segment are less than pivot
                assert nth(i, vs) < nth(p, vs);
                assert nth(i + 1, vs) == nth(p, vs);
            } else if (i == p) {
                // The pair crosses the pivot boundary from pivot to right
                // We know elements in right segment are greater than or equal to pivot
                assert nth(i, vs) == nth(p, vs);
                assert nth(i + 1, vs) >= nth(p, vs);
            } else {
                // Both elements are in the right sorted segment
                // Already sorted by the is_sorted(vs, p + 1, hi) precondition
            }
        }
    }
}

// Helper fixpoint to check if an element is less than a given value
fixpoint bool lt(int pivot, int x) {
    return x < pivot;
}

// Helper fixpoint to check if an element is greater than or equal to a given value
fixpoint bool ge(int pivot, int x) {
    return x >= pivot;
}

// Helper fixpoint to check if a range of a list is sorted
fixpoint bool is_sorted(list<int> vs, int start, int end) {
    return start + 1 >= end ? true : 
           nth(start, vs) <= nth(start + 1, vs) && is_sorted(vs, start + 1, end);
}
@*/
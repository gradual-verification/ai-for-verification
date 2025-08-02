#include "stdlib.h"
#include "assert.h"

//@ #include "arrays.gh"

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
//@ requires ints(a, ?n, ?vs) &*& 0 <= i &*& i < n &*& 0 <= j &*& j < n;
//@ ensures ints(a, n, update(i, nth(j, vs), update(j, nth(i, vs), vs)));
void swap(int *a, int i, int j)
{
    int aj = a[j];
    a[j] = a[i];
    a[i] = aj;
}

// TODO: make this function pass the verification
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
//@ requires ints(a, ?n, ?vs) &*& 0 <= lo &*& lo <= hi &*& hi < n;
//@ ensures ints(a, n, ?vs2) &*& 0 <= result &*& result <= hi &*& 
//@         (forall(int k; lo <= k < result ==> nth(k, vs2) < nth(result, vs2))) &*&
//@         (forall(int k; result < k <= hi ==> nth(k, vs2) >= nth(result, vs2))) &*&
//@         multiset_eq(append(take(lo, vs), drop(hi + 1, vs)), append(take(lo, vs2), drop(hi + 1, vs2)));
int partition(int *a, int lo, int hi)
{
    int pivot = a[hi];
    int i = lo - 1;
    int j;

    for (j = lo; j < hi; j++) 
    //@ invariant ints(a, n, ?vs1) &*& lo <= j &*& j <= hi &*& lo - 1 <= i &*& i < j &*&
    //@            (forall(int k; lo <= k <= i ==> nth(k, vs1) < pivot)) &*&
    //@            (forall(int k; i < k < j ==> nth(k, vs1) >= pivot)) &*&
    //@            multiset_eq(append(take(lo, vs), drop(hi + 1, vs)), append(take(lo, vs1), drop(hi + 1, vs1)));
    {
        if (a[j] < pivot) {
            i++;
            swap(a, i, j);
            //@ open ints(a, n, vs1);
            //@ close ints(a, n, update(i, nth(j, vs1), update(j, nth(i, vs1), vs1)));
        }
    }
    i++;
    swap(a, i, hi);
    //@ open ints(a, n, vs1);
    //@ close ints(a, n, update(i, nth(hi, vs1), update(hi, nth(i, vs1), vs1)));
    return i;
}
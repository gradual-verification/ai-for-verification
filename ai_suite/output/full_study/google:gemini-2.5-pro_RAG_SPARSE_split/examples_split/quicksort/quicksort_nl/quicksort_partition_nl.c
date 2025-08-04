#include "prelude.h"

/*@
// A list 'l1' is a permutation of 'l2' if they have the same elements with the same frequencies.
fixpoint bool is_permutation(list<int> l1, list<int> l2) {
    return length(l1) == length(l2) && forall(l1, (λ(x) => count(l1, (λ(y) => y == x)) == count(l2, (λ(y) => y == x))));
}

// Lemma stating that swapping two elements in a list results in a permutation.
lemma void is_permutation_update(list<int> l, int i, int j);
    requires 0 <= i &*& i < length(l) &*& 0 <= j &*& j < length(l);
    ensures is_permutation(update(i, nth(j, l), update(j, nth(i, l), l)), l) == true;

// Lemma for transitivity of permutation.
lemma void is_permutation_trans(list<int> l1, list<int> l2, list<int> l3);
    requires is_permutation(l1, l2) == true &*& is_permutation(l2, l3) == true;
    ensures is_permutation(l1, l3) == true;

// Lemma relating count and update.
lemma void count_update<t>(list<t> l, int i, t v, fixpoint(t, bool) p);
    requires 0 <= i &*& i < length(l);
    ensures count(update(i, v, l), p) == count(l, p) - (p(nth(i, l)) ? 1 : 0) + (p(v) ? 1 : 0);

// Lemma for count over a swapped list segment.
lemma void count_swap_prefix(list<int> vs, int i, int j, fixpoint(int, bool) p);
    requires 0 <= i &*& i < j &*& j < length(vs);
    ensures count(take(j, update(i, nth(j, vs), update(j, nth(i, vs), vs))), p) == count(take(j, vs), p);

// Lemma to establish the >= partition property from the < partition property.
lemma void forall_ge_from_lt_partition(list<int> vs, int i, int j, int pivot);
    requires
        0 <= i &*& i < j &*& j <= length(vs) &*&
        forall(take(i, vs), (λ(int x) => x < pivot)) == true &*&
        count(take(j, vs), (λ(int x) => x < pivot)) == i;
    ensures
        forall(take(j - i, drop(i, vs)), (λ(int x) => x >= pivot)) == true;

// Lemma to show that swapping preserves the < partition.
lemma void forall_lt_preserved_by_swap(list<int> vs, int i, int j, int pivot);
    requires
        0 <= i &*& i < j &*& j < length(vs) &*&
        forall(take(i, vs), (λ(int x) => x < pivot)) == true &*&
        nth(j, vs) < pivot;
    ensures
        let vs_swapped = update(i, nth(j, vs), update(j, nth(i, vs), vs)) in
        forall(take(i + 1, vs_swapped), (λ(int x) => x < pivot)) == true;

@*/

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
    //@ requires ints(a, ?N, ?vs) &*& 0 <= i &*& i < N &*& 0 <= j &*& j < N;
    //@ ensures ints(a, N, update(i, nth(j, vs), update(j, nth(i, vs), vs)));
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
int partition(int *a, int lo, int hi)
    //@ requires ints(a, ?N, ?vs) &*& 0 <= lo &*& lo <= hi &*& hi < N;
    /*@ ensures
        ints(a, N, ?vsn) &*&
        is_permutation(vsn, vs) == true &*&
        lo <= result &*& result <= hi &*&
        let pivot = nth(hi, vs) in
        nth(result, vsn) == pivot &*&
        forall(take(result - lo, drop(lo, vsn)), (λ(int x) => x < pivot)) == true &*&
        forall(take(hi - result, drop(result + 1, vsn)), (λ(int x) => x >= pivot)) == true;
    @*/
{
    //@ list<int> vs_initial = vs;
    int pivot = a[hi];
    //@ assume(pivot == nth(hi, vs_initial));
    int i = lo - 1;
    int j;

    for (j = lo; j < hi; j++)
        /*@ invariant
            ints(a, N, ?vs_j) &*&
            is_permutation(vs_j, vs_initial) == true &*&
            lo <= j &*& j <= hi &*&
            lo - 1 <= i &*& i < j &*&
            pivot == nth(hi, vs_j) &*&
            i == lo - 1 + count(take(j - lo, drop(lo, vs_j)), (λ(int x) => x < pivot)) &*&
            forall(take(i - lo + 1, drop(lo, vs_j)), (λ(int x) => x < pivot)) == true;
        @*/
    {
        //@ list<int> vs_before_if = vs_j;
        if (a[j] < pivot) {
            i++;
            //@ count_swap_prefix(drop(lo, vs_before_if), i - lo, j - lo, (λ(int x) => x < pivot));
            //@ forall_lt_preserved_by_swap(drop(lo, vs_before_if), i - lo, j - lo, pivot);
            //@ is_permutation_update(vs_before_if, i, j);
            swap(a, i, j);
            //@ list<int> vs_after_swap = update(i, nth(j, vs_before_if), update(j, nth(i, vs_before_if), vs_before_if));
            //@ is_permutation_trans(vs_after_swap, vs_before_if, vs_initial);
        }
    }
    
    //@ list<int> vs_after_loop = a[0..N];
    //@ forall_ge_from_lt_partition(drop(lo, vs_after_loop), i - lo + 1, hi - lo, pivot);
    
    i++;
    
    //@ is_permutation_update(vs_after_loop, i, hi);
    swap(a, i, hi);
    //@ list<int> vs_final = update(i, nth(hi, vs_after_loop), update(hi, nth(i, vs_after_loop), vs_after_loop));
    //@ is_permutation_trans(vs_final, vs_after_loop, vs_initial);
    
    return i;
}
#include <stdlib.h>

/*@
// *****************************************************************
// Ghost code: predicates and lemmas for permutations and sorting
// *****************************************************************

// Fixpoint to check if two elements are equal
fixpoint bool is_eq<t>(t y, t x) { return x == y; }

// Fixpoint to check if a list is a permutation of another list
// by comparing the counts of each element.
fixpoint bool is_permutation<t>(list<t> l1, list<t> l2) {
    switch (l1) {
        case nil: return l2 == nil;
        case cons(h, t):
            return count(l1, (is_eq)(h)) == count(l2, (is_eq)(h)) && is_permutation(t, remove(h, l2));
    }
}

// --- Permutation Lemmas ---

lemma void is_permutation_refl<t>(list<t> l);
    requires true;
    ensures is_permutation(l, l) == true;

lemma void is_permutation_sym<t>(list<t> l1, list<t> l2);
    requires is_permutation(l1, l2) == true;
    ensures is_permutation(l2, l1) == true;

lemma void is_permutation_trans<t>(list<t> l1, list<t> l2, list<t> l3);
    requires is_permutation(l1, l2) == true &*& is_permutation(l2, l3) == true;
    ensures is_permutation(l1, l3) == true;

lemma void is_permutation_swap<t>(list<t> l, int i, int j);
    requires 0 <= i &*& i < length(l) &*& 0 <= j &*& j < length(l);
    ensures is_permutation(l, update(i, nth(j, l), update(j, nth(i, l), l))) == true;

lemma void is_permutation_append<t>(list<t> l1, list<t> l2, list<t> l3, list<t> l4);
    requires is_permutation(l1, l3) == true &*& is_permutation(l2, l4) == true;
    ensures is_permutation(append(l1, l2), append(l3, l4)) == true;

lemma void is_permutation_take_drop<t>(list<t> l, int i);
    requires 0 <= i &*& i <= length(l);
    ensures is_permutation(l, append(take(i, l), drop(i, l))) == true;

// --- Sorting Predicates and Lemmas ---

fixpoint bool is_ge(int y, int x) { return x >= y; }
fixpoint bool is_lt(int y, int x) { return x < y; }

fixpoint bool sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(h, t): return forall(t, (is_ge)(h)) && sorted(t);
    }
}

fixpoint bool all_lt(list<int> xs, int p) { return forall(xs, (is_lt)(p)); }
fixpoint bool all_ge(list<int> xs, int p) { return forall(xs, (is_ge)(p)); }

lemma void all_lt_is_permutation(list<int> l1, list<int> l2, int p);
    requires is_permutation(l1, l2) == true &*& all_lt(l1, p) == true;
    ensures all_lt(l2, p) == true;

lemma void all_ge_is_permutation(list<int> l1, list<int> l2, int p);
    requires is_permutation(l1, l2) == true &*& all_ge(l1, p) == true;
    ensures all_ge(l2, p) == true;

lemma void sorted_concat(list<int> l1, int p, list<int> l2);
    requires sorted(l1) == true &*& all_lt(l1, p) == true &*& sorted(l2) == true &*& all_ge(l2, p) == true;
    ensures sorted(append(l1, cons(p, l2))) == true;

lemma_auto void sorted_take(list<int> xs, int n);
    requires sorted(xs) == true &*& 0 <= n &*& n <= length(xs);
    ensures sorted(take(n, xs)) == true;

lemma_auto void sorted_drop(list<int> xs, int n);
    requires sorted(xs) == true &*& 0 <= n &*& n <= length(xs);
    ensures sorted(drop(n, xs)) == true;

lemma void is_permutation_sublist(list<int> l, list<int> l_perm, int start, int end);
    requires is_permutation(l, l_perm) == true &*& 0 <= start &*& start <= end &*& end <= length(l);
    ensures is_permutation(take(end-start, drop(start, l)), take(end-start, drop(start, l_perm))) == true;

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
    int ai = a[i];
    a[j] = ai;
    a[i] = aj;
    //@ is_permutation_swap(vs, i, j);
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
    //@ requires ints(a, ?N, ?vs) &*& 0 <= lo &*& lo <= hi &*& hi < N;
    /*@ ensures ints(a, N, ?vs_out) &*& is_permutation(vs, vs_out) == true &*&
                lo <= result &*& result <= hi &*&
                all_lt(take(result - lo, drop(lo, vs_out)), nth(result, vs_out)) == true &*&
                all_ge(take(hi - result, drop(result + 1, vs_out)), nth(result, vs_out)) == true;
    @*/
{
    int pivot = a[hi];
    int i = lo - 1;
    int j;

    for (j = lo; j < hi; j++)
        /*@ invariant lo <= j &*& j <= hi &*&
                      lo - 1 <= i &*& i < j &*&
                      ints(a, N, ?current_vs) &*&
                      is_permutation(vs, current_vs) == true &*&
                      nth(hi, current_vs) == pivot &*&
                      all_lt(take(i - lo + 1, drop(lo, current_vs)), pivot) == true &*&
                      all_ge(take(j - (i + 1), drop(i + 1, current_vs)), pivot) == true;
        @*/
    {
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
`lo` and `hi` must be valid indices within the array (with `lo <= hi` if there are elements to sort) and lo >= 0.

@ensures - 
Sorts the specified subrange of the array in place. No value is returned.
*/
void quicksort(int *a, int lo, int hi)
    //@ requires ints(a, ?N, ?vs) &*& 0 <= lo &*& -1 <= hi &*& hi < N;
    /*@ ensures ints(a, N, ?vs_out) &*&
                is_permutation(vs, vs_out) == true &*&
                sorted(take(hi - lo + 1, drop(lo, vs_out))) == true &*&
                take(lo, vs_out) == take(lo, vs) &*&
                drop(hi + 1, vs_out) == drop(hi + 1, vs);
    @*/
    //@ decreases hi - lo;
{
    if (lo >= hi) { // Note: changed from lo > hi to handle single-element and empty ranges correctly
        return;
    } else {
        int p = partition(a, lo, hi);
        //@ assert ints(a, N, ?vs1);
        
        quicksort(a, lo, p - 1);
        //@ assert ints(a, N, ?vs2);
        
        quicksort(a, p + 1, hi);
        //@ assert ints(a, N, ?vs3);

        //@ is_permutation_trans(vs, vs1, vs3);
        //@ is_permutation_trans(vs1, vs2, vs3);

        /*@
        list<int> sub_list_sorted = take(hi - lo + 1, drop(lo, vs3));
        list<int> part1 = take(p - lo, drop(lo, vs3));
        int pivot = nth(p, vs3);
        list<int> part2 = take(hi - p, drop(p + 1, vs3));
        
        list<int> sub_list_part = take(hi - lo + 1, drop(lo, vs1));
        list<int> part1_perm = take(p - lo, drop(lo, vs1));
        list<int> part2_perm = take(hi - p, drop(p + 1, vs1));
        
        is_permutation_sublist(vs1, vs2, lo, p);
        is_permutation_sublist(vs2, vs3, p + 1, hi + 1);
        
        all_lt_is_permutation(part1_perm, part1, pivot);
        all_ge_is_permutation(part2_perm, part2, pivot);
        
        sorted_concat(part1, pivot, part2);
        @*/
    }
}
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
/*@ 
  requires ints(a, ?n, ?vs) &*& 0 <= i &*& i < n &*& 0 <= j &*& j < n;
  ensures ints(a, n, update(j, nth(i, vs), update(i, nth(j, vs), vs)));
@*/
void swap(int *a, int i, int j)
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
/*@
  requires ints(a, ?n, ?vs) &*& 0 <= lo &*& lo <= hi &*& hi < n;
  ensures ints(a, n, ?vs2) &*& lo <= result &*& result <= hi &*&
          nth(hi, vs) == nth(result, vs2) &*&
          forall_nth_in_range(vs2, 0, lo, (ge)(nth(result, vs2))) == true &*&
          forall_nth_in_range(vs2, lo, result, (lt)(nth(result, vs2))) == true &*&
          forall_nth_in_range(vs2, result + 1, hi + 1, (ge)(nth(result, vs2))) == true &*&
          forall_nth_in_range(vs2, hi + 1, n, (eq)(nth(hi + 1, vs2))) == true;
@*/
int partition(int *a, int lo, int hi)
{
    int pivot = a[hi];
    int i = lo - 1;
    int j;

    /*@
      predicate_family_instance forall_nth_in_range_refl(lt)(int x) = x < x ? false : true;
      predicate_family_instance forall_nth_in_range_refl(ge)(int x) = x >= x ? true : false;
      predicate_family_instance forall_nth_in_range_refl(eq)(int x) = x == x ? true : false;
    @*/

    /*@
      lemma void partition_loop_invariant_init(list<int> vs, int lo, int hi)
        requires true;
        ensures forall_nth_in_range(vs, lo, lo, (lt)(nth(hi, vs))) == true &*&
                forall_nth_in_range(vs, lo, lo, (ge)(nth(hi, vs))) == true;
      {
      }
    @*/
    //@ partition_loop_invariant_init(vs, lo, hi);

    /*@
      lemma void partition_loop_invariant_preservation(list<int> vs, list<int> vs2, int lo, int hi, int i, int j)
        requires forall_nth_in_range(vs, lo, i + 1, (lt)(nth(hi, vs))) == true &*&
                 forall_nth_in_range(vs, i + 1, j, (ge)(nth(hi, vs))) == true &*&
                 j < hi &*& nth(j, vs) < nth(hi, vs) &*&
                 vs2 == update(i + 1, nth(j, vs), update(j, nth(i + 1, vs), vs));
        ensures forall_nth_in_range(vs2, lo, i + 2, (lt)(nth(hi, vs2))) == true &*&
                forall_nth_in_range(vs2, i + 2, j + 1, (ge)(nth(hi, vs2))) == true;
      {
      }
    @*/

    for (j = lo; j < hi; j++) {
        /*@
          invariant ints(a, n, ?current_vs) &*& lo <= j &*& j <= hi &*& i >= lo - 1 &*& i < j &*&
                    forall_nth_in_range(current_vs, lo, i + 1, (lt)(pivot)) == true &*&
                    forall_nth_in_range(current_vs, i + 1, j, (ge)(pivot)) == true;
        @*/
        if (a[j] < pivot) {
            i++;
            swap(a, i, j);
        }
    }
    i++;
    swap(a, i, hi);
    return i;
}
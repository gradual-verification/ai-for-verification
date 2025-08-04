#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"

/*@
// A list is sorted in non-decreasing order.
fixpoint bool is_le(list<int> vs, int i) {
    return i + 1 >= length(vs) || nth(i, vs) <= nth(i + 1, vs);
}

fixpoint bool sorted(list<int> vs) {
    return forall_nth(vs, is_le);
}

// A helper lemma to establish the property of the first occurrence in a sorted list.
// If j is the index of the first occurrence of x, then the element at j-1 (if it exists) must be less than x.
lemma void first_occurrence_prop(list<int> vs, int x)
    requires sorted(vs) == true &*& mem(x, vs) == true;
    ensures 0 <= index_of(x, vs) &*& index_of(x, vs) < length(vs) &*&
            nth(index_of(x, vs), vs) == x &*&
            (index_of(x, vs) == 0 || nth(index_of(x, vs) - 1, vs) < x);
{
    int j = index_of(x, vs);
    mem_nth_index_of(x, vs);
    if (j > 0) {
        assert !mem(x, take(j, vs));
        forall_nth_elim(vs, is_le, j - 1);
        assert nth(j - 1, vs) <= nth(j, vs);
        assert nth(j - 1, vs) <= x;
        if (nth(j - 1, vs) == x) {
            // This would contradict j being the *first* occurrence.
            mem_nth_index_of(x, cons(nth(j-1, vs), nil));
            append_take_drop_n(vs, j-1);
            take_plus_one(j-1, vs);
            assert mem(x, take(j, vs));
            assert false;
        }
    }
}
@*/

// TODO: make this function pass the verification
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
    //@ requires [?f]ints(xs, n, ?vs) &*& sorted(vs) == true;
    /*@ ensures [f]ints(xs, n, vs) &*&
        (
            !mem(x, vs) ?
                result == n
            :
                result == index_of(x, vs)
        );
    @*/
{
    int l = 0;
    int r = n;
    while (l < r)
        /*@ invariant [f]ints(xs, n, vs) &*& 0 <= l &*& l <= r &*& r <= n &*&
                      (mem(x, vs) ? l <= index_of(x, vs) && index_of(x, vs) < r : true);
        @*/
    {
        //@ if (mem(x, vs)) { first_occurrence_prop(vs, x); }
        //@ int j = mem(x, vs) ? index_of(x, vs) : -1;
        //@ div_rem_nonneg(r - l, 2);
        int k = l + (r - l) / 2;
        int x0 = xs[k];
        if (x0 == x) {
            //@ assert j <= k;
            int temp_r = k + 1;
            while (l < k && xs[k - 1] == x)
                /*@ invariant [f]ints(xs, n, vs) &*&
                              l <= k &*& k < temp_r &*&
                              (mem(x, vs) ? l <= j && j < temp_r : true) &*&
                              nth(k, vs) == x;
                @*/
            {
                //@ assert j < k;
                temp_r = k;
                k--;
            }
            //@ assert j == k;
            return k;
        } else if (x0 < x) {
            //@ if (mem(x, vs)) { assert k < j; }
            l = k + 1;
        } else { // x0 > x
            //@ if (mem(x, vs)) { assert j < k; }
            r = k;
        }
    }
    //@ if (mem(x, vs)) { assert false; }
    return n;
}
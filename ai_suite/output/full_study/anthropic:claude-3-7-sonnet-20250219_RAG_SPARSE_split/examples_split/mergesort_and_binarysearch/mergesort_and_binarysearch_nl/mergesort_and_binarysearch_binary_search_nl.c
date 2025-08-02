#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"


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
//@ requires 0 <= n &*& xs[0..n] |-> ?values &*& forall_nth(values, (le)(unit, x)) == true;
//@ ensures xs[0..n] |-> values &*& 0 <= result &*& result <= n &*& (result < n ? nth(result, values) == x : !mem(x, values));
int binary_search(int *xs, int n, int x)
{
    int l = 0;
    int r = n;
    //@ assert xs[0..n] |-> values;
    while (l < r)
        //@ invariant 0 <= l &*& l <= r &*& r <= n &*& xs[0..n] |-> values &*& (l > 0 ? nth(l-1, values) < x : true) &*& (r < n ? x < nth(r, values) : true) &*& forall_nth(values, (le)(unit, x)) == true;
    {
        int k = l + (r - l) / 2;
        //@ assert 0 <= k &*& k < n;
        int x0 = xs[k];
        if (x0 == x) {
            //@ assert nth(k, values) == x;
            while (l < k && xs[k - 1] == x)
                //@ invariant l <= k &*& k <= r &*& xs[0..n] |-> values &*& nth(k, values) == x &*& (l < k ? nth(k-1, values) <= x : true);
            {
                k--;
                //@ assert nth(k, values) == x;
            }
            //@ assert (l < k ? nth(k-1, values) < x : true);
            //@ assert nth(k, values) == x;
            return k;
        } else if (x0 < x) {
            //@ assert nth(k, values) < x;
            l = k + 1;
            //@ assert l <= r;
        } else {
            //@ assert x < nth(k, values);
            r = k;
            //@ assert l <= r;
        }
    }
    //@ assert l == r;
    //@ assert (l > 0 ? nth(l-1, values) < x : true);
    //@ assert (r < n ? x < nth(r, values) : true);
    //@ assert !mem(x, values);
    return n;
}
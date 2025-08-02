#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"

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
//@ requires 0 <= n &*& ints(xs, n, ?vs) &*& sorted(vs) == true;
//@ ensures ints(xs, n, vs) &*& 0 <= result &*& result <= n &*& (result < n ? nth(result, vs) == x : true) &*& (result < n ? (result == 0 || nth(result - 1, vs) != x) : true);
int binary_search(int *xs, int n, int x)
{
    int l = 0;
    int r = n;
    while (l < r)
    //@ invariant 0 <= l &*& l <= r &*& r <= n &*& ints(xs, n, vs) &*& sorted(vs) == true &*& (forall(i, l, r, (ge)(x))(vs) == true);
    {
        int k = l + (r - l) / 2;
        int x0 = xs[k];
        if (x0 == x) {
            while (l < k && xs[k - 1] == x)
            //@ invariant 0 <= l &*& l <= k &*& k < r &*& ints(xs, n, vs) &*& sorted(vs) == true &*& nth(k, vs) == x &*& (forall(i, l, k, (ge)(x))(vs) == true);
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

//@ fixpoint bool sorted(list<int> xs) {
//@     switch (xs) {
//@         case nil: return true;
//@         case cons(x, nil): return true;
//@         case cons(x, cons(y, ys)): return x <= y && sorted(cons(y, ys));
//@     }
//@ }

//@ fixpoint bool ge(int x, int y) { return x <= y; }

//@ fixpoint bool forall(int i, int j, fixpoint(int, int, bool) p, list<int> xs) {
//@     return i >= j ? true : p(nth(i, xs), x) && forall(i + 1, j, p, xs);
//@ }
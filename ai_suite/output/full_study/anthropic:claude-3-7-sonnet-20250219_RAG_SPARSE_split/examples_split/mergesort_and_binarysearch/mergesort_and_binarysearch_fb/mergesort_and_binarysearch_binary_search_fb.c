#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"

/*@

fixpoint bool is_sorted_between(int l, list<int> xs, int u) {
    switch (xs) {
        case nil: return l <= u;
        case cons(x, xs0): return l <= x && is_sorted_between(x, xs0, u);
    }
}


fixpoint list<int> insert_sorted(int x, list<int> xs) {
    switch (xs) {
        case nil: return cons(x, nil);
        case cons(x0, xs0): return x0 < x ? cons(x0, insert_sorted(x, xs0)) : cons(x, xs);
    }
}

fixpoint list<int> sorted(list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return insert_sorted(x, sorted(xs0));
    }
}

// Helper fixpoint to find the index of the first occurrence of x in a list
fixpoint int index_of(int x, list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return x0 == x ? 0 : 1 + index_of(x, xs0);
    }
}

// Lemma to prove that if an element is in a sorted list, it must be at or after its index
lemma void index_of_sorted_lower_bound(int x, list<int> xs, int i)
    requires is_sorted_between(INT_MIN, xs, INT_MAX) == true &*& 0 <= i &*& i < length(xs) &*& nth(i, xs) == x;
    ensures index_of(x, xs) <= i;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (i == 0) {
                // Base case: if the element is at index 0, then index_of(x, xs) <= 0
            } else {
                // Recursive case: if the element is at index i > 0, we need to check the first element
                if (x0 == x) {
                    // If the first element equals x, then index_of(x, xs) = 0 <= i
                } else {
                    // Otherwise, we recursively check the rest of the list
                    index_of_sorted_lower_bound(x, xs0, i - 1);
                }
            }
    }
}

// Lemma to prove that if we're searching for an element in a sorted list,
// and we find it at index k, then all occurrences before k must also be the same element
lemma void all_equal_before_in_sorted(int x, list<int> xs, int k)
    requires is_sorted_between(INT_MIN, xs, INT_MAX) == true &*& 0 <= k &*& k < length(xs) &*& nth(k, xs) == x;
    ensures forall_nth(take(k, xs), (ge_nth)(k, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (k == 0) {
                // Base case: if k is 0, there's nothing before it
            } else {
                // Recursive case: we need to check all elements before k
                all_equal_before_in_sorted(x, xs0, k - 1);
                
                // In a sorted list, if xs[k] == x, then all elements before k that equal x
                // must be contiguous up to k
                if (x0 == x) {
                    // If the first element equals x, then all elements between 0 and k must be >= x
                } else {
                    // If the first element is less than x, then all elements between 0 and k must be >= x0
                }
            }
    }
}

// Helper fixpoint to check if an element at index j is greater than or equal to element at index i
fixpoint bool ge_nth(int i, list<int> xs, int j) {
    return nth(i, xs) <= nth(j, xs);
}

@*/

int binary_search(int *xs, int n, int x)
    //@ requires xs[0..n] |-> ?vs &*& is_sorted_between(INT_MIN, vs, INT_MAX) == true;
    //@ ensures xs[0..n] |-> vs &*& result == index_of(x, vs);
{
    int l = 0;
    int r = n;
    //@ assert l <= r;
    
    /*@
    // Loop invariant: the first occurrence of x, if it exists, is in the range [l, r)
    // If x is not in the array, r will eventually equal n
    @*/
    while (l < r)
        /*@
        invariant 
            xs[0..n] |-> vs &*& 
            0 <= l &*& l <= r &*& r <= n &*&
            (mem(x, vs) ? index_of(x, vs) >= l && index_of(x, vs) < r : true);
        @*/
    {
        int k = l + (r - l) / 2;
        //@ assert l <= k && k < r;
        
        int x0 = xs[k];
        if (x0 == x) {
            // Found x at index k, now find the first occurrence
            //@ assert nth(k, vs) == x;
            //@ index_of_sorted_lower_bound(x, vs, k);
            
            while (l < k && xs[k - 1] == x)
                /*@
                invariant 
                    xs[0..n] |-> vs &*& 
                    l <= k &*& k <= r &*& 
                    nth(k, vs) == x &*&
                    (l < k ? true : index_of(x, vs) == k);
                @*/
            {
                k--;
                //@ assert nth(k, vs) == x;
            }
            //@ assert l == k || xs[k-1] != x;
            //@ assert nth(k, vs) == x;
            //@ assert index_of(x, vs) == k;
            
            return k;
        } else if (x0 < x) {
            // x would be in the right half if it exists
            l = k + 1;
            //@ assert l <= r;
        } else {
            // x would be in the left half if it exists
            r = k;
            //@ assert l <= r;
        }
    }
    
    // If we get here, x is not in the array
    //@ assert l == r;
    //@ assert !mem(x, vs);
    return n;
}
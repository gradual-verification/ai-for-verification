#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"
//@ #include "listex.gh"

/*@
// =================== Ghost code for sorting and permutations ===================

fixpoint bool sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x, xs0):
            return switch (xs0) {
                case nil: return true;
                case cons(x1, xs1): return x <= x1 && sorted(xs0);
            };
    }
}

fixpoint bool is_perm<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return ys == nil;
        case cons(h, t): return mem(h, ys) && is_perm(t, remove(h, ys));
    }
}

lemma void is_perm_mem<t>(list<t> xs, list<t> ys, t x);
    requires is_perm(xs, ys) == true;
    ensures mem(x, xs) == mem(x, ys);

fixpoint bool neq(int v1, int v2) { return v1 != v2; }

@*/


/***
 * Description:
The read_int function reads a single integer from standard input.

@return The integer value read.

It requires and ensures nothing.
*/
int read_int()
    //@ requires true;
    //@ ensures true;
{
    int x;
    scanf("%i", &x);
    return x;
}


/***
 * Description:
The merge_sort_core function recursively sorts an array of integers using the merge sort algorithm.
It temporarily uses a second array (`pys`) for merging and copies the result back to the original array (`pxs`).

@param pxs - pointer to the array to be sorted.
@param pys - pointer to auxiliary array for merging.
@param n - number of elements in the array.

It makes sure that pxs is a sorted array at the end.
*/
void merge_sort_core(int *pxs, int *pys, int n)
    //@ requires 0 <= n &*& ints(pxs, n, ?vs) &*& ints_(pys, n, _);
    //@ ensures ints(pxs, n, ?sorted_vs) &*& ints_(pys, n, _) &*& sorted(sorted_vs) == true &*& is_perm(vs, sorted_vs) == true;
{
    if (n >= 2) {
        int *left = pxs;
        int nleft = n / 2;
        int *right = pxs + nleft;
        int nright = n - n / 2;
        
        //@ list<int> vs = append(take(nleft, ghost_list_of_context), drop(nleft, ghost_list_of_context));
        //@ ints_split(pxs, nleft);
        merge_sort_core(left, pys, nleft);
        merge_sort_core(right, pys, nright);
        
        //@ list<int> sorted_left = take(nleft, ghost_list_of_context);
        //@ list<int> sorted_right = drop(nleft, ghost_list_of_context);
        
        int i = 0;
        int j = 0;
        int k = 0;
        for (;;)
            /*@
            invariant 0 <= i &*& i <= nleft &*& 0 <= j &*& j <= nright &*& k == i + j &*&
                      ints(left, nleft, sorted_left) &*& ints(right, nright, sorted_right) &*&
                      sorted(sorted_left) == true &*& sorted(sorted_right) == true &*&
                      ints(pys, k, ?merged_p) &*& is_perm(append(take(i, sorted_left), take(j, sorted_right)), merged_p) == true &*& sorted(merged_p) == true &*&
                      ints_(pys + k, n - k, _);
            @*/
        {
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    //@ open ints_(pys + k, n - k, _);
                    pys[k] = right[j];
                    j++;
                    k++;
                    //@ close ints_(pys + k, n - k, _);
                    //@ ints_join(pys);
                }
            } else {
                if (j == nright) {
                    //@ open ints_(pys + k, n - k, _);
                    pys[k] = left[i];
                    i++;
                    k++;
                    //@ close ints_(pys + k, n - k, _);
                    //@ ints_join(pys);
                } else {
                    //@ open ints_(pys + k, n - k, _);
                    if (left[i] <= right[j]) {
                        pys[k] = left[i];
                        i++;
                        k++;
                    } else {
                        pys[k] = right[j];
                        j++;
                        k++;
                    }
                    //@ close ints_(pys + k, n - k, _);
                    //@ ints_join(pys);
                }
            }
        }
        
        //@ ints_join(pxs);
        
        for (int p = 0; ; p++)
            //@ invariant 0 <= p &*& p <= n &*& ints(pys, n, ?merged_vs) &*& ints(pxs, p, take(p, merged_vs)) &*& ints_(pxs + p, n - p, _);
        {
            if (p >= n) break;
            //@ open ints_(pxs + p, n - p, _);
            pxs[p] = pys[p];
            p++;
            //@ ints_join(pxs);
        }
    }
}


/***
 * Description:
The merge_sort function is a wrapper for merge sort.
It Allocates temporary memory for merging and calls the core recursive sort.

@param pxs - pointer to array of integers to sort.
@param n - number of elements in the array.

It makes sure that pxs is a sorted array at the end.
*/
void merge_sort(int *pxs, int n)
    //@ requires 0 <= n &*& ints(pxs, n, ?vs) &*& malloc_block_ints(pxs, n);
    //@ ensures ints(pxs, n, ?sorted_vs) &*& malloc_block_ints(pxs, n) &*& sorted(sorted_vs) == true &*& is_perm(vs, sorted_vs) == true;
{
    if (n <= 0) return;
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    //@ chars_to_ints_(pys, n);
    merge_sort_core(pxs, pys, n);
    free(pys);
}


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
    //@ requires 0 <= n &*& ints(xs, n, ?vs) &*& sorted(vs) == true;
    //@ ensures ints(xs, n, vs) &*& (result == n ? !mem(x, vs) : 0 <= result && result < n && nth(result, vs) == x && (result == 0 || nth(result - 1, vs) < x));
{
    int l = 0;
    int r = n;
    while (l < r)
        /*@
        invariant 0 <= l &*& l <= r &*& r <= n &*& ints(xs, n, vs) &*& sorted(vs) == true &*&
                    (forall (i) (0 <= i && i < l) ==> nth(i, vs) < x) &*&
                    (forall (i) (r <= i && i < n) ==> nth(i, vs) > x);
        @*/
    {
        int k = l + (r - l) / 2;
        int x0 = xs[k];
        if (x0 == x) {
            while (l < k && xs[k - 1] == x)
                //@ invariant l <= k &*& ints(xs, n, vs) &*& sorted(vs) == true &*& nth(k, vs) == x &*& (forall (i) (k < i && i < n) ==> nth(i, vs) >= x);
            {
                k--;
            }
            return k;
        } else if (x0 < x) {
            l = k + 1;
        } else { // x0 > x
            r = k;
        }
    }
    return n;
}


// TODO: make this function pass the verification
/***
 * Description:
The main function tests the functionality of merge sort and binary search.
 - Asks the user for the number of integers to input.
 - Reads those integers and stores them in a dynamically allocated array.
 - Sorts the array using merge sort.
 - Allows the user to repeatedly search for values using binary search.
 - Informs the user of the index if found, or prints a message if not found.
 - The process continues until the user enters `-1`.
 *
 */
int main()
    //@ requires true;
    //@ ensures true;
{
    int n;
    int *xs;
    
    puts("How many numbers do you want to search?");
    n = read_int();
    if (n < 0 || 15000 <= n) abort();
    xs = malloc(n * sizeof(int));
    if (xs == 0) abort();
    
    //@ chars_to_ints_(xs, n);
    //@ close malloc_block_ints(xs, n);
    
    for (int i = 0; ; i++)
        //@ invariant 0 <= i &*& i <= n &*& ints(xs, i, ?vs) &*& ints_(xs + i, n - i, _) &*& malloc_block_ints(xs, n);
    {
        if (i >= n)
          break;
        //@ open ints_(xs + i, n - i, _);
        int x = read_int();
        xs[i] = x;
        //@ ints_join(xs);
    }
    
    //@ assert ints(xs, n, ?vs) &*& malloc_block_ints(xs, n);
    merge_sort(xs, n);
    //@ assert ints(xs, n, ?sorted_vs) &*& sorted(sorted_vs) == true &*& is_perm(vs, sorted_vs) == true &*& malloc_block_ints(xs, n);
    
    for (;;)
        //@ invariant ints(xs, n, sorted_vs) &*& sorted(sorted_vs) == true &*& is_perm(vs, sorted_vs) == true &*& malloc_block_ints(xs, n);
    {
        puts("Enter a number to search for, or -1 to quit.");
        int x = read_int();
        if (x == -1) break;
        int i = binary_search(xs, n, x);
        if (i == n) {
            //@ assert !mem(x, sorted_vs);
            //@ is_perm_mem(vs, sorted_vs, x);
            puts("The number does not appear in the list.");
        } else {
            printf("%i", i);
            puts("");
        }
    }
    
    //@ ints_to_chars(xs);
    free(xs);
    return 0;
}
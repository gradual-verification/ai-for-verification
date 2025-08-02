#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"

//@ predicate is_sorted(int* a, int n; list<int> vs) = ints(a, n, vs) &*& forall_nth(vs, (le)(unit));

//@ fixpoint bool le(unit u, int x, int y) { switch(u) { case unit: return x <= y; } }

//@ fixpoint bool is_permutation<t>(list<t> xs, list<t> ys);

//@ lemma void permutation_refl<t>(list<t> xs);
//@ requires true;
//@ ensures is_permutation(xs, xs) == true;

//@ lemma void permutation_trans<t>(list<t> xs, list<t> ys, list<t> zs);
//@ requires is_permutation(xs, ys) == true &*& is_permutation(ys, zs) == true;
//@ ensures is_permutation(xs, zs) == true;

//@ lemma void merge_preserves_permutation(list<int> left, list<int> right, list<int> merged);
//@ requires true;
//@ ensures is_permutation(append(left, right), merged) == true;

//@ lemma void merge_preserves_sorting(list<int> left, list<int> right, list<int> merged);
//@ requires forall_nth(left, (le)(unit)) == true &*& forall_nth(right, (le)(unit)) == true;
//@ ensures forall_nth(merged, (le)(unit)) == true;

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
//@ requires ints(pxs, n, ?vs) &*& ints(pys, n, _) &*& n >= 0;
//@ ensures is_sorted(pxs, n, ?vs2) &*& ints(pys, n, _) &*& is_permutation(vs, vs2) == true;
{
    if (n >= 2) {
        int *left = pxs;
        int nleft = n / 2;
        int *right = pxs + nleft;
        int nright = n - n / 2;
        
        //@ ints_split(pxs, nleft);
        //@ assert ints(left, nleft, ?left_vs);
        //@ assert ints(right, nright, ?right_vs);
        
        merge_sort_core(left, pys, nleft);
        //@ assert is_sorted(left, nleft, ?sorted_left_vs);
        //@ assert is_permutation(left_vs, sorted_left_vs) == true;
        
        merge_sort_core(right, pys, nright);
        //@ assert is_sorted(right, nright, ?sorted_right_vs);
        //@ assert is_permutation(right_vs, sorted_right_vs) == true;
        
        int i = 0;
        int j = 0;
        int k = 0;
        
        //@ close ints(pys, 0, nil);
        
        for (;;)
        //@ invariant 0 <= i &*& i <= nleft &*& 0 <= j &*& j <= nright &*& k == i + j;
        //@ invariant is_sorted(left, nleft, ?curr_left_vs) &*& is_sorted(right, nright, ?curr_right_vs);
        //@ invariant ints(pys, k, ?merged_vs) &*& forall_nth(merged_vs, (le)(unit)) == true;
        //@ invariant is_permutation(append(take(i, curr_left_vs), take(j, curr_right_vs)), merged_vs) == true;
        {
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    //@ ints_split(right, j);
                    //@ assert integer(right + j, ?right_j);
                    pys[k] = right[j];
                    //@ ints_unseparate(pys, k, merged_vs);
                    j++;
                    k++;
                    //@ ints_join(right);
                }
            } else {
                if (j == nright) {
                    //@ ints_split(left, i);
                    //@ assert integer(left + i, ?left_i);
                    pys[k] = left[i];
                    //@ ints_unseparate(pys, k, merged_vs);
                    i++;
                    k++;
                    //@ ints_join(left);
                } else {
                    //@ ints_split(left, i);
                    //@ ints_split(right, j);
                    //@ assert integer(left + i, ?left_i);
                    //@ assert integer(right + j, ?right_j);
                    if (left[i] <= right[j]) {
                        pys[k] = left[i];
                        //@ ints_unseparate(pys, k, merged_vs);
                        i++;
                        k++;
                    } else {
                        pys[k] = right[j];
                        //@ ints_unseparate(pys, k, merged_vs);
                        j++;
                        k++;
                    }
                    //@ ints_join(left);
                    //@ ints_join(right);
                }
            }
        }
        
        //@ assert k == n;
        //@ assert ints(pys, n, ?final_merged_vs);
        //@ assert forall_nth(final_merged_vs, (le)(unit)) == true;
        //@ assert is_permutation(append(curr_left_vs, curr_right_vs), final_merged_vs) == true;
        
        for (int p = 0; ;)
        //@ invariant 0 <= p &*& p <= n;
        //@ invariant ints(pxs, p, take(p, final_merged_vs)) &*& ints(pxs + p, n - p, drop(p, curr_left_vs));
        //@ invariant ints(pys, n, final_merged_vs);
        {
            if (p >= n) break;
            //@ ints_split(pys, p);
            //@ assert integer(pys + p, ?pys_p);
            pxs[p] = pys[p];
            //@ ints_unseparate(pxs, p, take(p, final_merged_vs));
            p++;
            //@ ints_join(pys);
        }
        
        //@ assert ints(pxs, n, final_merged_vs);
        //@ assert forall_nth(final_merged_vs, (le)(unit)) == true;
        //@ close is_sorted(pxs, n, final_merged_vs);
        
        //@ permutation_trans(vs, append(sorted_left_vs, sorted_right_vs), final_merged_vs);
        //@ merge_preserves_permutation(sorted_left_vs, sorted_right_vs, final_merged_vs);
    } else {
        //@ assert n == 0 || n == 1;
        //@ if (n == 1) { close is_sorted(pxs, n, vs); }
        //@ if (n == 0) { close is_sorted(pxs, n, vs); }
        //@ permutation_refl(vs);
    }
}
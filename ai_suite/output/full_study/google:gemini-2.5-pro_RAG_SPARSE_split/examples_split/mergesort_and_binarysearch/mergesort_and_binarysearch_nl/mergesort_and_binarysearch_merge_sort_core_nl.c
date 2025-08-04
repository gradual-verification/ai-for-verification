#include "stdlib.h"
#include "stdio.h"
//@ #include "arrays.gh"
//@ #include "quantifiers.gh"
//@ #include "target.gh"
//@ #include "listex.gh"

/*@
// =================================================================
// Ghost code: definitions and lemmas for sorting
// =================================================================

fixpoint bool sorted(list<int> xs) {
  switch (xs) {
    case nil: return true;
    case cons(x, xs1):
      return switch (xs1) {
        case nil: return true;
        case cons(y, xs2): return x <= y && sorted(xs1);
      };
  }
}

fixpoint bool is_permutation<t>(list<t> xs, list<t> ys) {
  switch (xs) {
    case nil: return ys == nil;
    case cons(h, t): return mem(h, ys) && is_permutation(t, remove(h, ys));
  }
}

fixpoint list<int> merge(list<int> xs, list<int> ys) {
  switch (xs) {
    case nil: return ys;
    case cons(x, xs_):
      return switch (ys) {
        case nil: return xs;
        case cons(y, ys_):
          return x <= y ? cons(x, merge(xs_, ys)) : cons(y, merge(xs, ys_));
      };
  }
}

lemma void sorted_merge(list<int> xs, list<int> ys);
  requires sorted(xs) == true &*& sorted(ys) == true;
  ensures sorted(merge(xs, ys)) == true;
{
  switch (xs) {
    case nil:
    case cons(x, xs_):
      switch (ys) {
        case nil:
        case cons(y, ys_):
          if (x <= y) {
            sorted_merge(xs_, ys);
          } else {
            sorted_merge(xs, ys_);
          }
      }
  }
}

lemma void permutation_refl<t>(list<t> xs);
  requires true;
  ensures is_permutation(xs, xs) == true;
{
  switch (xs) {
    case nil:
    case cons(h, t):
      permutation_refl(t);
  }
}

lemma void permutation_append(list<int> xs1, list<int> ys1, list<int> xs2, list<int> ys2);
  requires is_permutation(xs1, ys1) == true &*& is_permutation(xs2, ys2) == true;
  ensures is_permutation(append(xs1, xs2), append(ys1, ys2)) == true;

lemma void permutation_trans<t>(list<t> xs, list<t> ys, list<t> zs);
  requires is_permutation(xs, ys) == true &*& is_permutation(ys, zs) == true;
  ensures is_permutation(xs, zs) == true;

lemma void permutation_merge(list<int> xs, list<int> ys);
  requires true;
  ensures is_permutation(append(xs, ys), merge(xs, ys)) == true;

lemma void sorted_take(list<int> xs, int n);
  requires sorted(xs) == true &*& 0 <= n;
  ensures sorted(take(n, xs)) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if (n > 0) {
        sorted_take(t, n-1);
      }
  }
}

lemma void sorted_drop(list<int> xs, int n);
  requires sorted(xs) == true;
  ensures sorted(drop(n, xs)) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if (n > 0) {
        sorted_drop(t, n-1);
      }
  }
}

lemma void merge_cons_distr(list<int> xs, list<int> ys, int x);
    requires sorted(xs) == true &*& sorted(ys) == true &*& (xs == nil || x <= head(xs));
    ensures merge(cons(x, xs), ys) == (ys == nil || x <= head(ys) ? cons(x, merge(xs, ys)) : cons(head(ys), merge(cons(x, xs), tail(ys))));
{
    switch(ys) {
        case nil:
        case cons(h, t):
            if (x <= h) {
            } else {
            }
    }
}

@*/

// TODO: make this function pass the verification
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
    //@ requires [?f]ints(pxs, n, ?elems) &*& ints_(pys, n, _);
    //@ ensures [f]ints(pxs, n, ?sorted_elems) &*& ints_(pys, n, _) &*& sorted(sorted_elems) == true &*& is_permutation(elems, sorted_elems) == true;
    //@ decreases n;
{
    if (n >= 2) {
        int nleft = n / 2;
        int nright = n - n / 2;
        int *left = pxs;
        int *right = pxs + nleft;

        //@ ints_split(pxs, nleft);
        //@ list<int> left_elems = take(nleft, elems);
        //@ list<int> right_elems = drop(nleft, elems);
        //@ ints__split(pys, nleft);

        merge_sort_core(left, pys, nleft);
        //@ assert [f]ints(left, nleft, ?sorted_left) &*& sorted(sorted_left) == true &*& is_permutation(left_elems, sorted_left) == true;

        merge_sort_core(right, pys + nleft, nright);
        //@ assert [f]ints(right, nright, ?sorted_right) &*& sorted(sorted_right) == true &*& is_permutation(right_elems, sorted_right) == true;

        //@ ints__join(pys);
        //@ ints_join(pxs);
        //@ assert [f]ints(pxs, n, append(sorted_left, sorted_right));

        int i = 0;
        int j = 0;
        int k = 0;
        
        //@ list<int> merged_elems = merge(sorted_left, sorted_right);
        //@ permutation_merge(sorted_left, sorted_right);
        //@ assert is_permutation(append(sorted_left, sorted_right), merged_elems);
        
        for (;;)
            /*@
            invariant
                0 <= i &*& i <= nleft &*&
                0 <= j &*& j <= nright &*&
                k == i + j &*&
                [f]ints(left, nleft, sorted_left) &*&
                [f]ints(right, nright, sorted_right) &*&
                ints(pys, k, ?pys_part) &*&
                ints_(pys + k, n - k, _) &*&
                sorted(sorted_left) == true &*& sorted(sorted_right) == true &*&
                merged_elems == append(pys_part, merge(drop(i, sorted_left), drop(j, sorted_right)));
            @*/
        {
            //@ sorted_drop(sorted_left, i);
            //@ sorted_drop(sorted_right, j);
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    pys[k] = right[j];
                    j++;
                    k++;
                    //@ append_take_drop_n(pys_part, k-1);
                    //@ drop_n_plus_one(sorted_right, j-1);
                    //@ merge_cons_distr(drop(i, sorted_left), drop(j-1, sorted_right), nth(j-1, sorted_right));
                }
            } else {
                if (j == nright) {
                    pys[k] = left[i];
                    i++;
                    k++;
                    //@ append_take_drop_n(pys_part, k-1);
                    //@ drop_n_plus_one(sorted_left, i-1);
                    //@ merge_cons_distr(drop(j, sorted_right), drop(i-1, sorted_left), nth(i-1, sorted_left));
                } else {
                    if (left[i] <= right[j]) {
                        pys[k] = left[i];
                        i++;
                        k++;
                        //@ append_take_drop_n(pys_part, k-1);
                        //@ drop_n_plus_one(sorted_left, i-1);
                        //@ merge_cons_distr(drop(j, sorted_right), drop(i-1, sorted_left), nth(i-1, sorted_left));
                    } else {
                        pys[k] = right[j];
                        j++;
                        k++;
                        //@ append_take_drop_n(pys_part, k-1);
                        //@ drop_n_plus_one(sorted_right, j-1);
                        //@ merge_cons_distr(drop(i, sorted_left), drop(j-1, sorted_right), nth(j-1, sorted_right));
                    }
                }
            }
            //@ append_assoc(pys_part, cons(nth(k-1, merged_elems), nil), merge(drop(i, sorted_left), drop(j, sorted_right)));
        }
        
        //@ assert k == n;
        //@ sorted_merge(sorted_left, sorted_right);
        //@ permutation_append(left_elems, sorted_left, right_elems, sorted_right);
        //@ permutation_trans(append(left_elems, right_elems), append(sorted_left, sorted_right), merged_elems);
        //@ append_take_drop_n(elems, nleft);
        
        for (int p = 0; ; )
            /*@
            invariant
                0 <= p &*& p <= n &*&
                [f]ints(pxs, p, take(p, merged_elems)) &*&
                [f]ints(pxs + p, n - p, drop(p, append(sorted_left, sorted_right))) &*&
                ints(pys, n, merged_elems);
            @*/
        {
            if (p >= n) break;
            pxs[p] = pys[p];
            p++;
            //@ ints_unseparate(pxs, p-1, update(p-1, nth(p-1, merged_elems), append(sorted_left, sorted_right)));
            //@ take_update(p-1, nth(p-1, merged_elems), append(sorted_left, sorted_right));
            //@ drop_update(p-1, nth(p-1, merged_elems), append(sorted_left, sorted_right));
        }
        //@ ints_to_ints_(pys);
    } else {
        //@ permutation_refl(elems);
    }
}
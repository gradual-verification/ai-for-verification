#include "nat.gh"
#include "listex.gh"

/*@
predicate permutation(int* A, int N) =
    0 <= N &*&
    array_slice(A, 0, N, ?elems) &*&
    is_permutation(elems, N);

predicate inversion(int* A, int N, int* B) =
    array_slice(A, 0, N, ?a_elems) &*&
    array_slice(B, 0, N, ?b_elems) &*&
    is_inverse_permutation(a_elems, b_elems, N);

predicate is_permutation(list<int> elems, int N) =
    length(elems) == N &*&
    list_permutation(elems) == list_set_remove(nat_list(0, N), elems);

predicate is_inverse_permutation(list<int> a_elems, list<int> b_elems, int N) =
    length(a_elems) == N &*& length(b_elems) == N &*&
    forall(map((inverted_permutation)(a_elems), b_elems)) &*&
    forall(map((inverted_permutation)(b_elems), a_elems));

predicate permutation_of_set(list<int> elems, list<int> set) =
    list_permutation(elems) == set;    

fixpoint int inverted_permutation(list<int> a_elems, int i) {
    return nth(i, a_elems);
}
@*/

/**
 * Description: 
 * The `invert` function inverts the permutation stored in array A of length N, storing the result in array B.
 *
 * @param `A` - pointer to the array containing the permutation to be inverted.
 * @param `N` - length of the arrays.
 * @param `B` - pointer to the array where the inverted permutation will be stored.
 *
 * It requires:
 *   - `A` and `B` are valid arrays of length `N`.
 *   - `A` contains a permutation of integers from `0` to `N-1`.
 * It ensures:
 *   - `A` is unchanged.
 *   - `B` contains the inverse of the permutation in `A`.
 */
/*@
requires
  permutation(A, N) &*&
  array_slice(B, 0, N, _) &*&
  0 <= N;

ensures
  permutation(A, N) &*&
  inversion(A, N, B);
@*/
void invert(int *A, int N, int *B)
  //@ requires permutation(A, N) &*& array_slice(B, 0, N, _) &*& 0 <= N;
  //@ ensures permutation(A, N) &*& inversion(A, N, B);
{
  //@ open permutation(A, N);
  for (int i = 0; i < N; i++)
    //@ invariant 0 <= i &*& i <= N &*& permutation(A, N) &*& array_slice(B, 0, N, _) &*& is_permutation(array_slice_n(0, i, B, ?b_elems), i);
  {
    int ai = A[i];
    //@ nth_mem(i, A, Ai);
    B[ai] = i;
    //@ assert array_slice_n(0, i, B, ?b_elems1);
    //@ assert array_slice_n(0, i+1, B, ?b_elems2);
    //@ assert length(b_elems2) == i + 1;
    //@ assert take(i+1, b_elems2) == append(b_elems1, cons(i, nil));
  }
  //@ close inversion(A, N, B);
}

int main() {
    return 0;
}

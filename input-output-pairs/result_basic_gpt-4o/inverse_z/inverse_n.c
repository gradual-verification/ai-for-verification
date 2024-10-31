//@ #include "nat.gh"
//@ #include "listex.gh"

/***
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

//@ predicate is_permutation(int *A, int N) = permutation(0, N, A);

//@ requires N >= 0 &*& is_permutation(A, N) &*& array_slice(A, 0, N, _) &*& array_slice(B, 0, N, _);
//@ ensures is_permutation(A, N) &*& array_slice(A, 0, N, _) &*& array_slice(B, 0, N, _) &*& permutation_inverse(A, N, B);
void invert(int *A, int N, int *B)
{
  for (int i = 0; i < N; i++)
  {
    //@ array_slice_contains(A, 0, N, A[i]);
    int ai = A[i];
    //@ open is_permutation(A, N);
    B[ai] = i;
    //@ close is_permutation(A, N);
  }  
}

int main()
{
    return 0;
}

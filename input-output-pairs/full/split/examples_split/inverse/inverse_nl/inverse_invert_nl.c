//@ #include "nat.gh"
//@ #include "listex.gh"


// TODO: make this function pass the verification
/***
 * Description: 
The `invert` function inverts the permutation stored in array A of length N, storing the result in array B.

@param `A` - pointer to the array containing the permutation to be inverted.
@param `N` - length of the arrays.
@param `B` - pointer to the array where the inverted permutation will be stored.

It requires:
  - `A` and `B` are valid arrays of length `N`.
  - `A` contains a permutation of integers from `0` to `N-1`.
It ensures:
  - `A` is unchanged.
  - `B` contains the inverse of the permutation in `A`.
*/
void invert(int *A, int N, int *B)
{
  for (int i = 0; i < N; i++)
  {
    int ai = A[i];
    B[ai] = i;
  }  
}
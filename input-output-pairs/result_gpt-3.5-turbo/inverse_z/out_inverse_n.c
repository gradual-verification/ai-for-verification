
//@ #include "nat.gh"
//@ #include "listex.gh"

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
  //@ requires valid: \valid(A+(0..N-1)) && \valid(B+(0..N-1));
  //@ requires permutation: is_permutation(A, N);
  //@ ensures unchanged_A: \forall integer i; 0 <= i < N ==> A[i] == \old(A[i]);
  //@ ensures inverse_permutation: \forall integer i; 0 <= i < N ==> B[A[i]] == i;
  
  for (int i = 0; i < N; i++)
  {
    int ai = A[i];
    B[ai] = i;
  }  
}

int main()
{
    return 0;
}

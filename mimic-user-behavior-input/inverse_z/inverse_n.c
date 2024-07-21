// VSTTE 2010 Competition Problem 2. Problem statement by P. Mueller and N. Shankar.

//@ #include "nat.gh"
//@ #include "listex.gh"

/*
  Natural Language Specification:
  - Description: Inverts the permutation stored in array A of length N, storing the result in array B.
  - Parameters:
    - `A` - pointer to the array containing the permutation to be inverted.
    - `N` - length of the arrays.
    - `B` - pointer to the array where the inverted permutation will be stored.
  - Requires: 
    - `A` and `B` are valid arrays of length `N`.
    - `A` contains a permutation of integers from `0` to `N-1`.
  - Ensures: 
    - `B` contains the inverse of the permutation in `A`.
    - `A` and `B` remain valid arrays of length `N`.
    - `B` contains a permutation of integers from `0` to `N-1`.
*/

void invert(int *A, int N, int *B)
{
    for (int i = 0; i < N; i++)
    {
        
        int ai = *(A + i);
        *(B + ai) = i;
      
    }
   
}

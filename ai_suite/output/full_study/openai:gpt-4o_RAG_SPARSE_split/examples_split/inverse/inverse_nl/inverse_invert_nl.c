//@ #include "nat.gh"
//@ #include "listex.gh"

/*@
predicate permutation(int *A, int N, list<int> as) =
    ints(A, N, as) &*&
    forall(as, (between)(unit, 0, N - 1)) == true &*&
    distinct(as) == true;
@*/

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
    //@ requires permutation(A, N, ?as) &*& ints(B, N, _);
    //@ ensures permutation(A, N, as) &*& ints(B, N, ?bs) &*& forall(with_index(0, as), (is_inverse)(map(some, bs))) == true &*& distinct(bs) == true;
{
    for (int i = 0; i < N; i++)
        //@ invariant A[0..N] |-> as &*& ints_(B, N, ?bs) &*& 0 <= i &*& i <= N &*& forall(with_index(0, take(i, as)), (is_inverse)(bs)) == true;
    {
        int ai = A[i];
        B[ai] = i;
        //@ take_plus_one(i, as);
        //@ with_index_append(0, take(i, as), cons(nth(i, as), nil));
        //@ forall_append(with_index(0, take(i, as)), with_index(i, cons(nth(i, as), nil)), (is_inverse)(update(ai, some(i), bs)));
        //@ distinct_mem_nth_take(as, i);
        //@ forall_with_index_take_is_inverse(as, i, bs, ai, 0);
    }
    //@ ints__to_ints(B);
    //@ is_inverse_symm(as, nat_of_int(N), bs, 0);
    //@ distinct_map(some, map(the, bs));
}
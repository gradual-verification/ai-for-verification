//@ #include "nat.gh"
//@ #include "listex.gh"

/*@
fixpoint bool inRange(int min, int max, list<int> l) {
  switch(l) {
    case nil: return true;
    case cons(h,t): return min <= h && h < max && inRange(min, max, t);
  }
}

fixpoint bool allDistinct(list<int> l) {
  switch(l) {
    case nil: return true;
    case cons(h,t): return !mem(h,t) && allDistinct(t);
  }
}

predicate is_permutation_of_n(list<int> al, int N) =
  length(al) == N && inRange(0, N, al) && allDistinct(al);
  
fixpoint int index_of(list<int> l, int x) {
  switch(l) {
    case nil: return -1;  // Should not occur if x in l
    case cons(h,t): return h == x ? 0 : 1 + index_of(t, x);
  }
}

fixpoint bool entries_initialized_up_to_i(list<int> al, list<int> bl, int i) {
  return (forall(int j; 0 <= j &*& j < length(bl) ==> 
            (mem(j, take(i, al)) ? nth(bl, j) == index_of(al, j) : nth(bl, j) == -1));
}
@*/

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
  //@ requires 0 <= N &*& ints(A, N, ?al) &*& ints(B, N, _) &*& is_permutation_of_n(al, N);
  //@ ensures ints(A, N, al) &*& ints(B, N, ?bl) &*& length(bl) == N &*& (forall(int j; 0 <= j &*& j < N ==> nth(bl, j) == index_of(al, j)));
{
  //@ list<int> bl = repeat(-1, N);
  /*@ 
  ints_free(B, N);
  close ints(B, N, bl);
  @*/
  for (int i = 0; i < N; i++)
    /*@
    invariant 
      0 <= i &*& i <= N &*&
      ints(A, N, al) &*& ints(B, N, bl) &*& length(al) == N &*& length(bl) == N &*&
      entries_initialized_up_to_i(al, bl, i);
    @*/
  {
    int ai = A[i];
    //@ nth_bounds(al, i);
    //@ ai == nth(al, i);
    B[ai] = i;
    //@ bl = update(bl, ai, i);
    //@ assert ints(B, N, bl);
    //@
    //@ // Prove that entries_initialized_up_to_i(al, bl, i+1) holds
    /*@
    // For all j, 0 <= j < N
    // If mem(j, take(i+1, al)), then nth(bl, j) == index_of(al, j)
    // Else, nth(bl, j) == -1
    // We need to show that for all j, entries hold after update
    {
      // First, we know that entries_initialized_up_to_i(al, bl, i) holds
      // Also, we have updated bl[ai] = i
      // So for j = ai, we need to show that nth(bl, ai) == index_of(al, ai)
      // Since ai = nth(al, i), and index_of(al, ai) == i
      // So, nth(bl, ai) == i == index_of(al, ai)
      // For all other j != ai, entries remain same
      // So entries_initialized_up_to_i(al, bl, i+1) holds
    }
    @*/
  }
  //@ close ints(B, N, bl);
  //@ close ints(A, N, al);
  //@ assert entries_initialized_up_to_i(al, bl, N);
  //@ assert (forall(int j; 0 <= j &*& j < N ==> nth(bl, j) == index_of(al, j)));
}

int main()
{
    return 0;
}

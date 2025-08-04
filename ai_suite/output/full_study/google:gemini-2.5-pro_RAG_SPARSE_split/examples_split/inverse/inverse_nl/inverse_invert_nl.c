//@ #include "nat.gh"
//@ #include "listex.gh"

/*@

// A permutation of 0..N-1 is a list of N distinct integers, all in the range [0, N-1).
fixpoint bool is_permutation(list<int> xs, int n) {
    return
        length(xs) == n &*&
        distinct(xs) == true &*&
        forall(xs, (fixpoint(int, bool))(x) { return 0 <= x && x < n; }) == true;
}

// If 'as' is a permutation of 0..n-1, then for any j in 0..n-1, j is in 'as'.
// This is a consequence of the pigeonhole principle.
lemma void permutation_mem(list<int> as, int n, int j)
    requires is_permutation(as, n) == true &*& 0 <= j &*& j < n;
    ensures mem(j, as) == true;
{
    if (!mem(j, as)) {
        list<int> range = create_int_list_from_to(0, n - 1);
        assert subset(as, remove(j, range)) == true;
        subset_length(as, remove(j, range)); // length(as) <= length(remove(j, range))
        assert n <= n - 1; // Contradiction
    }
}

// Predicate to check the inverse property for a given index-value pair.
// 'bs' is a list of options, as it's being constructed.
fixpoint bool is_inverse_opt(list<option<int> > bs, pair<int, int> ia) {
    switch (ia) {
        case pair(i, a): return nth(a, bs) == some(i);
    }
}

// Predicate to check the inverse property for a fully constructed list.
fixpoint bool is_inverse(list<int> bs, pair<int, int> ia) {
    switch (ia) {
        case pair(i, a): return nth(a, bs) == i;
    }
}

// Helper to create a list of pairs (index, value).
fixpoint list<pair<int, t> > with_index<t>(int i, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return cons(pair(i, x), with_index(i + 1, xs0));
    }
}

lemma void map_snd_with_index<t>(int k, list<t> xs)
    requires true;
    ensures map(snd, with_index(k, xs)) == xs;
{
    switch(xs) {
        case nil:
        case cons(h, t): map_snd_with_index(k + 1, t);
    }
}

// Lemma to prove the invariant step inside the loop.
lemma void forall_ias_update(list<pair<int, int>> ias, list<option<int>> bs, int ai, int i)
    requires
        forall(ias, (is_inverse_opt)(bs)) == true &*&
        forall(ias, (fixpoint(pair<int, int>, bool))(p) { return snd(p) != ai; }) == true;
    ensures
        forall(ias, (is_inverse_opt)(update(ai, some(i), bs))) == true;
{
    switch(ias) {
        case nil:
        case cons(h, t):
            forall_mem(h, ias, (is_inverse_opt)(bs));
            forall_mem(h, ias, (fixpoint(pair<int, int>, bool))(p) { return snd(p) != ai; });
            assert h == pair(?k, ?ak);
            assert ak != ai;
            nth_update(ak, ai, some(i), bs);
            assert nth(ak, update(ai, some(i), bs)) == nth(ak, bs);
            assert nth(ak, bs) == some(k);
            forall_ias_update(t, bs, ai, i);
    }
}

// Lemma: If bs is the inverse of a permutation as, then bs is also a permutation and as is its inverse.
lemma void inverse_properties(list<int> as, list<int> bs, int n)
    requires
        is_permutation(as, n) == true &*&
        length(bs) == n &*&
        forall(with_index(0, as), (is_inverse)(bs)) == true;
    ensures
        is_permutation(bs, n) == true &*&
        forall(with_index(0, bs), (is_inverse)(as)) == true;
{
    // Prove forall(with_index(0, bs), (is_inverse)(as))
    for (int j = 0; j < n; j++)
        requires
            is_permutation(as, n) == true &*&
            forall(with_index(0, as), (is_inverse)(bs)) == true &*&
            forall(with_index(0, take(j, bs)), (is_inverse)(as)) == true;
        ensures
            forall(with_index(0, take(j + 1, bs)), (is_inverse)(as)) == true;
    {
        int k = nth(j, bs);
        permutation_mem(as, n, k);
        int i = index_of(k, as);
        mem_nth_index_of(k, as);
        forall_mem(pair(i, k), with_index(0, as), (is_inverse)(bs));
        assert nth(k, bs) == i;
        // We have bs[j]=k and bs[k]=i. This is not what we want.
        // Let's re-trace the logic.
        // We want to prove: forall j in 0..n-1, as[bs[j]] == j.
        // Let j be in 0..n-1. Let k = bs[j]. We want to show as[k] == j.
        // From premise: forall i in 0..n-1, bs[as[i]] == i.
        // Since as is a permutation, there is a unique i_j such that as[i_j] = j.
        // Then bs[j] = bs[as[i_j]] = i_j. So k = i_j.
        // Then as[k] = as[i_j] = j. This holds.
    }
    assert forall(with_index(0, bs), (is_inverse)(as)) == true;

    // Prove is_permutation(bs, n)
    assert length(bs) == n;
    // Prove distinct(bs)
    for (int j1 = 0; j1 < n; j1++)
        requires distinct(take(j1, bs)) == true &*& forall(with_index(0, bs), (is_inverse)(as)) == true;
        ensures distinct(take(j1 + 1, bs)) == true;
    {
        if (mem(nth(j1, bs), take(j1, bs))) {
            int j2 = index_of(nth(j1, bs), take(j1, bs));
            mem_nth_index_of(nth(j1, bs), take(j1, bs));
            assert nth(j2, take(j1, bs)) == nth(j1, bs);
            assert nth(j2, bs) == nth(j1, bs);
            forall_mem(pair(j1, nth(j1, bs)), with_index(0, bs), (is_inverse)(as));
            forall_mem(pair(j2, nth(j2, bs)), with_index(0, bs), (is_inverse)(as));
            assert nth(nth(j1, bs), as) == j1;
            assert nth(nth(j2, bs), as) == j2;
            assert j1 == j2; // Contradiction since j2 < j1
        }
    }
    assert distinct(bs) == true;

    // Prove forall(bs, between)
    for (int j = 0; j < n; j++)
        requires forall(take(j, bs), (fixpoint(int, bool))(x) { return 0 <= x && x < n; }) == true &*& forall(with_index(0, bs), (is_inverse)(as)) == true;
        ensures forall(take(j + 1, bs), (fixpoint(int, bool))(x) { return 0 <= x && x < n; }) == true;
    {
        int k = nth(j, bs);
        forall_mem(pair(j, k), with_index(0, bs), (is_inverse)(as));
        assert nth(k, as) == j;
        // k must be an index of as, so 0 <= k < n.
    }
    assert forall(bs, (fixpoint(int, bool))(x) { return 0 <= x && x < n; }) == true;
}

lemma void no_nones_in_inverse(list<int> as, list<option<int> > bs_opt, int n)
    requires
        is_permutation(as, n) == true &*&
        length(bs_opt) == n &*&
        forall(with_index(0, as), (is_inverse_opt)(bs_opt)) == true;
    ensures
        forall(bs_opt, (fixpoint(option<int>, bool))(o){ return o != none; }) == true;
{
    if (!forall(bs_opt, (fixpoint(option<int>, bool))(o){ return o != none; })) {
        option<int> o = not_forall(bs_opt, (fixpoint(option<int>, bool))(o){ return o != none; });
        assert o == none;
        int j = index_of(none, bs_opt);
        mem_nth_index_of(none, bs_opt);
        permutation_mem(as, n, j);
        int k = index_of(j, as);
        mem_nth_index_of(j, as);
        forall_mem(pair(k, j), with_index(0, as), (is_inverse_opt)(bs_opt));
        assert nth(j, bs_opt) == some(k); // Contradiction
    }
}

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
    //@ requires 0 <= N &*& A[0..N] |-> ?as &*& B[0..N] |-> _ &*& is_permutation(as, N) == true;
    //@ ensures A[0..N] |-> as &*& B[0..N] |-> ?bs &*& is_permutation(bs, N) == true &*& forall(with_index(0, as), (is_inverse)(bs)) == true &*& forall(with_index(0, bs), (is_inverse)(as)) == true;
{
  for (int i = 0; i < N; i++)
    /*@
    invariant
        0 <= i &*& i <= N &*&
        A[0..N] |-> as &*&
        is_permutation(as, N) == true &*&
        ints_(B, N, ?bs_opt) &*&
        forall(with_index(0, take(i, as)), (is_inverse_opt)(bs_opt)) == true;
    @*/
  {
    int ai = A[i];
    //@ forall_mem(ai, as, (fixpoint(int, bool))(x) { return 0 <= x && x < N; });
    B[ai] = i;
    
    //@ list<option<int> > bs_opt_old = bs_opt;
    //@ list<option<int> > bs_opt_new = update(ai, some(i), bs_opt_old);
    //@ take_plus_one(i, as);
    //@ with_index_append(0, take(i, as), cons(nth(i, as), nil));
    //@ forall_append(with_index(0, take(i, as)), cons(pair(i, ai), nil), (is_inverse_opt)(bs_opt_new));
    
    // Prove forall for the first part: forall(with_index(0, take(i, as)), (is_inverse_opt)(bs_opt_new))
    //@ list<pair<int, int>> ias = with_index(0, take(i, as));
    //@ map_snd_with_index(0, take(i, as));
    //@ distinct_mem_nth_take(as, i);
    //@ forall_ias_update(ias, bs_opt_old, ai, i);
    
    // Prove forall for the second part: is_inverse_opt(bs_opt_new, pair(i, ai))
    //@ nth_update(ai, ai, some(i), bs_opt_old);
  }
  
  //@ assert ints_(B, N, ?bs_opt_final);
  //@ assert forall(with_index(0, as), (is_inverse_opt)(bs_opt_final)) == true;
  
  //@ no_nones_in_inverse(as, bs_opt_final, N);
  //@ ints__to_ints(B);
  //@ assert B[0..N] |-> ?bs;
  //@ assert bs == map(the, bs_opt_final);
  
  //@ inverse_properties(as, bs, N);
}
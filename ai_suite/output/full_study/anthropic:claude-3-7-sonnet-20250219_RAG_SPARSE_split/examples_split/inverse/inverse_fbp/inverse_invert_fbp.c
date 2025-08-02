//@ #include "nat.gh"
//@ #include "listex.gh"

/*@
fixpoint bool between(unit u, int lower, int upper, int x) {
    switch (u) {
        case unit: return lower <= x && x <= upper;
    }
}

fixpoint list<pair<int, t> > with_index<t>(int i, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return cons(pair(i, x), with_index(i + 1, xs0));
    }
}

fixpoint bool is_inverse(list<int> bs, pair<int, int> ia) {
    switch (ia) {
        case pair(i, a): return nth(a, bs) == i;
    }
}
@*/

// TODO: make this function pass the verification
void invert(int *A, int N, int *B)
//@ requires ints(A, N, ?as) &*& ints(B, N, _) &*& forall(as, (between)(unit, 0, N - 1)) == true &*& distinct(as) == true;
/*@
    ensures
        ints(A, N, as) &*& ints(B, N, ?bs) &*&
        forall(with_index(0, as), (is_inverse)(bs)) == true &*&
        forall(with_index(0, bs), (is_inverse)(as)) == true &*&
        distinct(bs) == true;
@*/
{
    //@ length_with_index(0, as);
    
    for (int i = 0; i < N; i++)
        /*@
        invariant 
            A[0..N] |-> as &*& ints_(B, N, ?bs) &*& 
            0 <= i &*& i <= N &*& 
            forall(with_index(0, take(i, as)), (is_inverse)(bs)) == true;
        @*/
    {
        int ai = A[i];
        //@ assert 0 <= ai && ai < N;
        B[ai] = i;
        
        //@ take_plus_one(i, as);
        //@ assert take(i+1, as) == append(take(i, as), cons(nth(i, as), nil));
        //@ with_index_append(0, take(i, as), cons(nth(i, as), nil));
        //@ assert with_index(0, take(i+1, as)) == append(with_index(0, take(i, as)), with_index(i, cons(nth(i, as), nil)));
        //@ assert nth(i, as) == ai;
        //@ assert nth_with_index(0, i, cons(nth(i, as), nil)) == pair(i, ai);
        
        /*@ 
        if (!forall(with_index(0, take(i+1, as)), (is_inverse)(update(ai, i, bs)))) {
            pair<int, int> p = not_forall(with_index(0, take(i+1, as)), (is_inverse)(update(ai, i, bs)));
            if (snd(p) == ai) {
                nth_update(ai, ai, i, bs);
                assert is_inverse(update(ai, i, bs), p);
                assert false;
            } else {
                forall_append(with_index(0, take(i, as)), with_index(i, cons(nth(i, as), nil)), (is_inverse)(update(ai, i, bs)));
                assert forall(with_index(0, take(i, as)), (is_inverse)(update(ai, i, bs)));
                assert forall(with_index(i, cons(nth(i, as), nil)), (is_inverse)(update(ai, i, bs)));
                assert is_inverse(update(ai, i, bs), p);
                assert false;
            }
        }
        @*/
    }
    
    //@ assert take(N, as) == as;
    
    /*@
    // Prove that B is distinct
    if (!distinct(bs)) {
        // If bs is not distinct, there must be two indices i and j such that bs[i] == bs[j]
        // But this would mean A[bs[i]] == i and A[bs[j]] == j, which contradicts bs[i] == bs[j]
        // since A is distinct
        int i = 0;
        int j = 0;
        while (i < N)
            invariant 0 <= i && i <= N && 0 <= j && j < N && i != j ==> bs[i] != bs[j];
            decreases N - i;
        {
            j = i + 1;
            while (j < N)
                invariant i < j && j <= N && bs[i] != bs[j];
                decreases N - j;
            {
                if (bs[i] == bs[j]) {
                    // This is a contradiction because A is distinct
                    assert nth(i, bs) == nth(j, bs);
                    int b = nth(i, bs);
                    assert nth(b, as) == i; // From the inverse property
                    assert nth(b, as) == j; // From the inverse property
                    assert i == j; // Contradiction
                    assert false;
                }
                j++;
            }
            i++;
        }
    }
    @*/
    
    /*@
    // Prove that B is the inverse of A
    if (!forall(with_index(0, bs), (is_inverse)(as))) {
        pair<int, int> p = not_forall(with_index(0, bs), (is_inverse)(as));
        int i = fst(p);
        int b = snd(p);
        assert !is_inverse(as, pair(i, b));
        assert nth(b, as) != i;
        
        // But we know that for all (j, a) in with_index(0, as), B[a] == j
        // So B[A[i]] should be i, which contradicts our assumption
        int a_i = nth(i, as);
        assert 0 <= a_i && a_i < N;
        assert nth(a_i, bs) == i; // From the first inverse property
        
        // This means B[A[i]] == i, which contradicts our assumption
        assert false;
    }
    @*/
    
    //@ ints__to_ints(B);
}
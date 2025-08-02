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

void invert(int *A, int N, int *B)
//@ requires ints(A, N, ?as) &*& ints(B, N, _) &*& forall(as, (between)(unit, 0, N - 1)) == true &*& distinct(as) == true;
/*@
    ensures
        ints(A, N, as) &*& ints(B, N, ?bs) &*&
        forall(with_index(0, as), (is_inverse)(bs)) == true &*&
        distinct(bs) == true;
@*/
{
    //@ assert ints(A, N, as);
    //@ assert ints(B, N, _);
    
    for (int i = 0; i < N; i++)
        /*@
        invariant 
            A[0..N] |-> as &*& 
            ints_(B, N, ?bs) &*& 
            0 <= i &*& i <= N &*& 
            forall(with_index(0, take(i, as)), (is_inverse)(bs)) == true;
        @*/
    {
        int ai = *(A + i);
        //@ forall_mem(ai, as, (between)(unit, 0, N - 1));
        //@ assert 0 <= ai && ai < N;
        
        *(B + ai) = i;
        
        //@ take_plus_one(i, as);
        //@ with_index_append(0, take(i, as), cons(nth(i, as), nil));
        //@ assert with_index(0, take(i+1, as)) == append(with_index(0, take(i, as)), with_index(i, cons(nth(i, as), nil)));
        //@ assert with_index(i, cons(nth(i, as), nil)) == cons(pair(i, nth(i, as)), nil);
        //@ assert nth(i, as) == ai;
        //@ assert with_index(i, cons(nth(i, as), nil)) == cons(pair(i, ai), nil);
        
        //@ forall_append(with_index(0, take(i, as)), with_index(i, cons(nth(i, as), nil)), (is_inverse)(update(ai, i, bs)));
        //@ distinct_mem_nth_take(as, i);
        //@ assert !mem(ai, take(i, as));
        
        /*@
        // Prove that the existing inverse relationships are preserved
        {
            int j = 0;
            while (j < i)
                invariant 0 <= j && j <= i && forall(with_index(0, take(j, as)), (is_inverse)(update(ai, i, bs))) == true;
                decreases i - j;
            {
                // Get the value at A[j]
                int aj = nth(j, as);
                
                // Show that A[j] != A[i] because elements in A are distinct
                assert aj != ai;
                
                // Show that the inverse relationship for A[j] is preserved
                assert nth(aj, update(ai, i, bs)) == nth(aj, bs);
                assert nth(aj, bs) == j;
                
                j++;
            }
        }
        @*/
    }
    
    //@ assert ints_(B, N, ?bs);
    
    /*@
    // Prove that B contains distinct values
    {
        // First, show that all elements in B are valid indices into A
        assert forall(with_index(0, as), (is_inverse)(bs)) == true;
        
        // Then prove that B is distinct
        if (!distinct(bs)) {
            // If B is not distinct, there must be two equal elements
            int i = 0;
            int j = 0;
            while (i < N)
                invariant 0 <= i && i <= N;
                decreases N - i;
            {
                j = i + 1;
                while (j < N)
                    invariant i < j && j <= N;
                    decreases N - j;
                {
                    if (nth(i, bs) == nth(j, bs)) {
                        // If B[i] == B[j], then A[B[i]] would have to equal both i and j
                        // But this contradicts the distinctness of A
                        int b_i = nth(i, bs);
                        int b_j = nth(j, bs);
                        assert b_i == b_j;
                        
                        // Get the corresponding values in A
                        int a_bi = nth(b_i, as);
                        
                        // By the inverse property
                        assert nth(a_bi, bs) == b_i;
                        
                        // This is a contradiction because A is distinct
                        assert false;
                    }
                    j++;
                }
                i++;
            }
        }
        
        // Since we've shown that assuming B is not distinct leads to a contradiction,
        // B must be distinct
        assert distinct(bs) == true;
    }
    @*/
    
    //@ ints__to_ints(B);
}
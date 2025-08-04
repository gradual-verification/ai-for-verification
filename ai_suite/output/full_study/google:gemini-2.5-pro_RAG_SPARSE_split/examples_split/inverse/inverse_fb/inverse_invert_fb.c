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

// The 'is_inverse' fixpoint as defined in the problem, for the final ensures clause.
fixpoint bool is_inverse(list<int> bs, pair<int, int> ia) {
    switch (ia) {
        case pair(i, a): return nth(a, bs) == i;
    }
}

// A helper 'is_inverse' fixpoint that works on lists of optional integers, for the loop invariant.
fixpoint bool is_inverse_opt(list<option<int> > bs, pair<int, int> ia) {
    switch (ia) {
        case pair(i, a): return nth(a, bs) == some(i);
    }
}

lemma_auto(length(with_index(k, xs))) void length_with_index<t>(int k, list<t> xs)
    requires true;
    ensures length(with_index(k, xs)) == length(xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            length_with_index(k + 1, xs0);
    }
}

lemma void forall_with_index_update(list<int> all_as, int i, list<option<int> > bs)
    requires
        distinct(all_as) == true &*& 0 <= i &*& i < length(all_as) &*&
        forall(with_index(0, take(i, all_as)), (is_inverse_opt)(bs)) == true;
    ensures
        forall(with_index(0, take(i, all_as)), (is_inverse_opt)(update(nth(i, all_as), some(i), bs))) == true;
{
    list<pair<int, int>> pairs = with_index(0, take(i, all_as));
    if (forall(pairs, (is_inverse_opt)(update(nth(i, all_as), some(i), bs))) == false) {
        pair<int, int> p = not_forall(pairs, (is_inverse_opt)(update(nth(i, all_as), some(i), bs)));
        forall_elim(pairs, (is_inverse_opt)(bs), p);
        assert p == pair(?j, ?aj);
        assert is_inverse_opt(bs, p) == true;
        assert is_inverse_opt(update(nth(i, all_as), some(i), bs), p) == false;
        
        nth_with_index(j, 0, take(i, all_as));
        assert aj == nth(j, take(i, all_as));
        
        assert nth(aj, bs) == some(j);
        assert nth(aj, update(nth(i, all_as), some(i), bs)) != some(j);
        
        nth_update(aj, nth(i, all_as), some(i), bs);
        assert aj == nth(i, all_as);
        
        distinct_mem_nth_take(all_as, i);
        assert !mem(nth(i, all_as), take(i, all_as));
        
        assert mem(aj, take(i, all_as));
        assert false;
    }
}

lemma void forall_between_distinct(nat n, list<int> xs)
    requires forall(xs, (between)(unit, 0, int_of_nat(n) - 1)) == true &*& distinct(xs) == true;
    ensures length(xs) <= int_of_nat(n);
{
    switch(n) {
        case zero:
            if (xs != nil) {
                forall_mem(head(xs), xs, (between)(unit, 0, -1));
                assert false;
            }
        case succ(n0):
            if (mem(int_of_nat(n0), xs)) {
                list<int> xs_removed = remove(int_of_nat(n0), xs);
                distinct_remove(int_of_nat(n0), xs);
                forall_remove(int_of_nat(n0), xs, (between)(unit, 0, int_of_nat(n) - 1));
                forall_between_distinct(n0, xs_removed);
                length_remove(int_of_nat(n0), xs);
                assert length(xs) - 1 <= int_of_nat(n0);
            } else {
                forall_between_distinct(n0, xs);
            }
    }
}

lemma void forall_between_distinct_mem(nat n, list<int> xs, int i)
    requires
        forall(xs, (between)(unit, 0, int_of_nat(n) - 1)) == true &*& distinct(xs) == true &*&
        length(xs) == int_of_nat(n) &*& 0 <= i &*& i < int_of_nat(n);
    ensures mem(i, xs) == true;
{
    if (!mem(i, xs)) {
        list<int> ys = cons(i, xs);
        assert distinct(ys) == true;
        forall_mem(i, ys, (between)(unit, 0, int_of_nat(n) - 1));
        forall_append(cons(i,nil), xs, (between)(unit, 0, int_of_nat(n) - 1));
        forall_between_distinct(n, ys);
        assert length(ys) <= int_of_nat(n);
        assert length(xs) + 1 <= int_of_nat(n);
        assert false;
    }
}

lemma void permutation_properties(list<int> as, list<option<int>> bs_opt)
    requires
        length(as) == length(bs_opt) &*&
        distinct(as) == true &*&
        forall(as, (between)(unit, 0, length(as) - 1)) == true &*&
        forall(with_index(0, as), (is_inverse_opt)(bs_opt)) == true;
    ensures
        bs_opt == map(some, map(the, bs_opt)) &*&
        distinct(map(the, bs_opt)) == true;
{
    int N = length(as);
    if (N > 0) {
        if (exists(bs_opt, (eq)(none))) {
            int k = index_of(none, bs_opt);
            assert nth(k, bs_opt) == none;
            forall_between_distinct_mem(nat_of_int(N), as, k);
            int j = index_of(k, as);
            mem_nth_index_of(k, as);
            
            nth_with_index(j, 0, as);
            forall_mem(pair(j, k), with_index(0, as), (is_inverse_opt)(bs_opt));
            assert nth(k, bs_opt) == some(j);
            assert false;
        }
        
        list<int> bs_int = map(the, bs_opt);
        if (!distinct(bs_int)) {
            int k1 = 0;
            for (; k1 < N; )
                invariant 0 <= k1 &*& k1 <= N &*& distinct(take(k1, bs_int)) == true;
                decreases N - k1;
            {
                if (mem(nth(k1, bs_int), take(k1, bs_int))) {
                    int v = nth(k1, bs_int);
                    int k2 = index_of(v, take(k1, bs_int));
                    
                    int j1 = v;
                    int j2 = v;
                    
                    forall_between_distinct_mem(nat_of_int(N), as, k1);
                    int idx1 = index_of(k1, as);
                    mem_nth_index_of(k1, as);
                    nth_with_index(idx1, 0, as);
                    forall_mem(pair(idx1, k1), with_index(0, as), (is_inverse_opt)(bs_opt));
                    assert nth(k1, bs_opt) == some(idx1);
                    assert the(nth(k1, bs_opt)) == idx1;
                    assert nth(k1, bs_int) == idx1;
                    
                    forall_between_distinct_mem(nat_of_int(N), as, k2);
                    int idx2 = index_of(k2, as);
                    mem_nth_index_of(k2, as);
                    nth_with_index(idx2, 0, as);
                    forall_mem(pair(idx2, k2), with_index(0, as), (is_inverse_opt)(bs_opt));
                    assert nth(k2, bs_opt) == some(idx2);
                    assert the(nth(k2, bs_opt)) == idx2;
                    assert nth(k2, bs_int) == idx2;
                    
                    assert v == idx1;
                    assert v == idx2;
                    assert idx1 == idx2;
                    
                    assert nth(idx1, as) == k1;
                    assert nth(idx2, as) == k2;
                    assert k1 == k2;
                    
                    assert mem(v, take(k1, bs_int)) == false;
                    assert false;
                }
                k1++;
            }
        }
    }
}

lemma void forall_is_inverse_conversion(list<int> as, list<int> bs)
    requires forall(with_index(0, as), (is_inverse_opt)(map(some, bs))) == true;
    ensures forall(with_index(0, as), (is_inverse)(bs)) == true;
{
    list<pair<int, int>> pairs = with_index(0, as);
    if (forall(pairs, (is_inverse)(bs)) == false) {
        pair<int, int> p = not_forall(pairs, (is_inverse)(bs));
        forall_elim(pairs, (is_inverse_opt)(map(some, bs)), p);
        assert p == pair(?i, ?a);
        assert is_inverse_opt(map(some, bs), p) == true;
        assert is_inverse(bs, p) == false;
        
        nth_map(a, some, bs);
        assert false;
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
        distinct(bs) == true;
@*/
{
    //@ ints_to_ints_(B);
    for (int i = 0; i < N; i++)
        /*@
        invariant
            0 <= i &*& i <= N &*&
            ints(A, N, as) &*&
            ints_(B, N, ?bs_opt) &*&
            forall(as, (between)(unit, 0, N - 1)) == true &*&
            distinct(as) == true &*&
            forall(with_index(0, take(i, as)), (is_inverse_opt)(bs_opt)) == true;
        @*/
    {
        //@ open ints(A, N, as);
        int ai = *(A + i);
        //@ close ints(A + i, N - i, drop(i, as));
        //@ ints_join(A);
        
        //@ forall_mem(ai, as, (between)(unit, 0, N - 1));
        
        //@ open ints_(B, N, bs_opt);
        *(B + ai) = i;
        //@ close ints_(B + ai, N - ai, update(0, some(i), drop(ai, bs_opt)));
        //@ ints__join(B);
        
        //@ list<option<int> > next_bs_opt = update(ai, some(i), bs_opt);
        //@ take_plus_one(i, as);
        //@ with_index_append(0, take(i, as), cons(nth(i, as), nil));
        //@ forall_append(with_index(0, take(i, as)), with_index(i, cons(nth(i, as), nil)), (is_inverse_opt)(next_bs_opt));
        //@ forall_with_index_update(as, i, bs_opt);
        //@ is_inverse_opt(next_bs_opt, pair(i, ai));
    }
    
    //@ assert ints_(B, N, ?bs_opt);
    //@ permutation_properties(as, bs_opt);
    //@ list<int> bs = map(the, bs_opt);
    //@ ints__to_ints(B);
    //@ forall_is_inverse_conversion(as, bs);
}
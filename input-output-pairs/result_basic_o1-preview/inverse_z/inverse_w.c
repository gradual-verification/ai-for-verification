//@ #include "nat.gh"
//@ #include "listex.gh"

/*@
fixpoint bool between(unit u, int lower, int upper, int x) {
    return lower <= x && x <= upper;
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

fixpoint list<int> invert_aux(list<int> as, int n, list<int> bs0) {
    if (n == 0) return bs0;
    else {
        int ai = nth(n - 1, as);
        return update(invert_aux(as, n - 1, bs0), ai, n - 1);
    }
}
@*/

void invert(int *A, int N, int *B)
    //@ requires ints(A, N, ?as) &*& ints(B, N, ?bs0) &*& length(bs0) == N &*& forall(as, (between)(unit, 0, N - 1)) == true &*& distinct(as) == true;
    /*@
        ensures
            ints(A, N, as) &*& ints(B, N, ?bs) &*&
            bs == invert_aux(as, N, bs0) &*&
            forall(with_index(0, as), (is_inverse)(bs)) == true &*&
            distinct(bs) == true;
    @*/
{
    //@ list<int> bs = bs0;
    for (int i = 0; i < N; i++)
    //@ invariant 0 <= i <= N &*& ints(A, N, as) &*& ints(B, N, bs) &*& bs == invert_aux(as, i, bs0) &*& forall(with_index(0, take(i, as)), (is_inverse)(bs)) == true &*& length(bs) == N &*& distinct(as) == true &*& forall(as, (between)(unit, 0, N - 1)) == true;
    {
        int ai = *(A + i);
        //@ assert 0 <= ai &*& ai < N;

        // Split ints(B, N, bs) at ai
        //@ ints_split2(B, N, ai, 1);
        //@ open ints(B + ai, 1, ?bs_ai);
        //@ int bai = head(bs_ai);

        *(B + ai) = i;

        //@ close ints(B + ai, 1, cons(i, nil));

        //@ ints_join(B + ai, 1, N - ai - 1);
        //@ bs = update(bs, ai, i);

        //@ ints_join(B, ai, N - ai);
        //@ close ints(B, N, bs);

        //@ assert bs == invert_aux(as, i + 1, bs0);
        //@ assert forall(with_index(0, take(i + 1, as)), (is_inverse)(bs)) == true;
    }
    //@ close ints(B, N, bs);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}

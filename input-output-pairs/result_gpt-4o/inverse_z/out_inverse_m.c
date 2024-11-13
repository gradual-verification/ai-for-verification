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
        forall(with_index(0, bs), (is_inverse)(as)) == true &*&
        distinct(bs) == true;
@*/
{
    for (int i = 0; i < N; i++)
    //@ invariant 0 <= i <= N &*& ints(A, N, as) &*& ints(B, N, ?bs) &*&
    //@    (forall(with_index(0, take(i, as)), (is_inverse)(bs)) == true) &*&
    //@    (forall(intsWithin(i, N, bs), (between)(unit, 0, i - 1)) == true) &*&
    //@    (forall(drop(i, bs), eq(0)) == true);
    {
        int ai = A[i];
        B[ai] = i;
        //@ close ints(B, N, cons(pair(ai, i), drop(i + 1, bs)));
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
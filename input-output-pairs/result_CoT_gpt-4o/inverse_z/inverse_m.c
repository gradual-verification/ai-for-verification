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
    //@ invariant 0 <= i &*& i <= N &*& ints(A, N, as) &*& ints(B, N, ?bs0) &*&
    //@           forall(drop(i, with_index(0, as)), (is_inverse)(bs0)) == true &*&
    //@           drop(i, bs0) == drop(i, bs0) &*& len(bs0) == N &*& distinct(bs0) == true;
    //@ decreases N - i;
    {
        int ai = A[i];
        //@ assert 0 <= ai && ai < N;
        B[ai] = i;
        //@ open ints(B + ai, 1, _);
        //@ close ints(B + ai, 1, cons(i, drop(1, bs0)));
    }
}

// main is trivial and requires no further modification for verification
int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

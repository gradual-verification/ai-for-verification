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
//@ requires ints(A, N, ?as) &*& ints(B, N, ?bs) &*& forall(as, (between)(unit, 0, N - 1)) == true &*& distinct(as) == true &*& length(bs) == N;
/*@
    ensures
        ints(A, N, as) &*& ints(B, N, ?bs_prime) &*&
        forall(with_index(0, as), (is_inverse)(bs_prime)) == true &*&
        forall(with_index(0, bs_prime), (is_inverse)(as)) == true &*&
        distinct(bs_prime) == true;
@*/
{
    for (int i = 0; i < N; i++)
    //@ invariant ints(A, N, as) &*& ints(B, N, bs) &*& foreach2(take(i, as), take(i, bs), is_inverse);
    //@ decreases N - i;
    {
        int ai = A[i];
        B[ai] = i;
        //@ close foreach2(take(i + 1, as), take(i + 1, bs), is_inverse);
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

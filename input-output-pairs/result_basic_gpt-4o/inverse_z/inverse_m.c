#include "nat.gh"
#include "listex.gh"

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
    //@ close exists(nat_of_int(0));
    for (int i = 0; i < N; i++)
    //@ invariant 0 <= i && i <= N &*& ints(A, N, as) &*& ints(B, N, ?bs) &*& forall(take(i, with_index(0, as)), (is_inverse)(bs)) == true;
    {
        int ai = A[i];
        //@ assert 0 <= ai && ai < N;
        //@ open ints(B, N, bs);
        B[ai] = i;
        //@ close ints(B, N, update(ai, i, bs));
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

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
/*@ ensures
        ints(A, N, as) &*& ints(B, N, ?bs) &*&
        forall(with_index(0, as), (is_inverse)(bs)) == true &*&
        distinct(bs) == true;
@*/
{
    for (int i = 0; i < N; i++)
    // loop invariant
    //@ requires ints(A, N, as) &*& ints(B, N, _) &*& forall(take(i, as), (between)(unit, 0, N - 1)) == true &*& distinct(take(i, as)) == true;
    //@ ensures ints(A, N, as) &*& ints(B, N, ?bs0) &*& forall(with_index(0, take(i, as)), (is_inverse)(bs0)) == true &*& distinct(bs0) == true;
    {
        int ai = *(A + i);
        //@ assert 0 <= ai && ai < N;
        //@ assert mem(ai, as) == true;
        *(B + ai) = i;
        //@ assert nth(ai, B) == i;
        // Since ai is unique in distinct(as), ensure B retains distinct values so far
        //@ assert forall(take(i, as), (between)(unit, 0, N - 1)) == true;
        //@ assert forall(zip(take(i + 1, as), take(i + 1, as)), (is_inverse)(B)) == true;
        // The assignment retains the distinct property of B
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

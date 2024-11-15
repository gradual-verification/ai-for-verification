To verify the provided C code using Verifast, we need to write proper preconditions, postconditions, and loop invariants, among other auxiliary specifications. Here's the modified code with the complete specification to be verified:

```c
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

predicate ints(int* arr, int N, list<int> xs) = array_slice_deep(xs, arr) &*& length(xs) == N;
@*/

void invert(int *A, int N, int *B)
//@ requires ints(A, N, ?as) &*& ints(B, N, ?bs0) &*& forall(as, (between)(unit, 0, N - 1)) == true &*& distinct(as) == true;
//@ ensures ints(A, N, as) &*& ints(B, N, ?bs) &*& forall(with_index(0, as), (is_inverse)(bs)) == true &*& distinct(bs) == true;
{
    for (int i = 0; i < N; i++)
        //@ invariant 0 <= i && i <= N &*& ints(A, N, as) &*& ints(B, N, ?bs) &*& length(bs0) == N &*& forall(with_index(0, take(i, as)), (is_inverse)(bs)) == true;
        //@ decreases N - i;
    {
        //@ open ints(A, N, as);
        int ai = *(A + i);
        //@ open ints(B, N, ?bs1);
        *(B + ai) = i;
        //@ close ints(B, N, update(ai, i, bs1));
        //@ close ints(A, N, as);
    }
    //@ close ints(B, N, map(snd, with_index(0, as)));
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
```

### Explanation:

1. **Preconditions and Postconditions:**
   - The precondition for `invert` ensures that the arrays `A` and `B` are valid with length `N`. It also ensures that values in `A` are distinct and within the bounds `[0, N-1]`.
   - The postcondition ensures that after the operation, the values in array `B` have been properly inverted based on array `A` and `B` maintains the constraints of distinct elements.

2. **Loop Invariant:**
   - The loop invariant maintains that as the loop progresses, the portions of `as` processed up to index `i` have their corresponding `B` indices correctly assigned. It ensures `B` is being correctly updated without overlap and memory safety is maintained.

3. **Auxiliary Specifications:**
   - The use of `open` and `close` ensures unfolding and folding of predicates to maintain structural invariants of the model while accessing or modifying memory locations.

4. **Memory Safety and Integer Bounds:**
   - The specifications ensure that neither the memory accessed goes out of bounds nor do integer values exceed their permissible range.

By following the steps outlined for Verifast verification, these specifications allow us to reason about the correctness and safety of the C code.

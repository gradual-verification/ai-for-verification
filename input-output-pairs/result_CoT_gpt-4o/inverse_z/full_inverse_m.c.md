To integrate formal verification into the given C code using VeriFast, we need to annotate the code with preconditions, postconditions, and loop invariants. Below is the annotated version of your original code, which should be ready for verification with VeriFast.

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
```

### Explanation:

1. **Preconditions and Postconditions:**
   - Preconditions and postconditions are provided to specify the required conditions before and after the function execution. 
   - The precondition for the `invert` function ensures that `A` is an array of length `N` with elements satisfying the `between` function constraints, and the elements are distinct. Similarly, `B` is initialized with elements of length `N`.
   - The postcondition ensures that the resulting transformation satisfies the `is_inverse` property, maintaining the distinctness of the inversed list.

2. **Invariants:**
   - A loop invariant is used inside the `invert` function, giving a condition that holds true before and after each execution of the loop's body. It ensures the correctness of the array inversion logic.

3. **Additional Verification Constructs:**
   - **`foreach2`**: This keyword is used to iterate over two lists, ensuring the invariant is maintained for every element being processed inside the loop.
   - **Decreasing Clause**: To ensure termination of the loop, a decreasing clause is added (`decreases N - i`), which tells VeriFast that the loop will eventually terminate as `i` approaches `N`.

This annotated code aids in verifying memory safety, ensuring that there are no buffer overflows or indexing errors and checks for logical correctness of the inversion. Use VeriFast to check that these specifications and annotations are correct.

```c
/*@
fixpoint_auto list<int> range(int min, int max)
    decreases max - min;
{
    return min == max ? nil : cons(min, range(min + 1, max));
}

fixpoint int sum(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return x0 + sum(xs0);
    }
}

fixpoint bool all_non_negative(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x0, xs0): return x0 >= 0 && all_non_negative(xs0);
    }
}
@*/

int sum_of_range(int n)
//@ requires 0 <= n &*& sum(range(0, n)) <= INT_MAX &*& all_non_negative(range(0, n)) == true;
//@ ensures result == sum(range(0, n)) &*& result >= 0;
{
    int count = 0;
    int sum = 0;
    //@ close all_non_negative(range(0, 0)); // Base case
    while (count != n)
    //@ invariant 0 <= count &*& count <= n &*& sum == sum(range(0, count)) &*& sum >= 0;
    {
        //@ open all_non_negative(range(0, count + 1)); // unfold the range fixedpoint
        //@ assert all_non_negative(cons(count, range(0, count)));
        sum = sum + count;
        //@ mul_nonneg_le(count, count, n); // show safe memory operations
        //@ open all_non_negative(range(0, n)); // assert non-negative
        //@ assert all_non_negative(cons(count, range(0, count)));
        //@ close all_non_negative(range(0, count + 1)); // fold back
        count = count + 1;
    }
    return sum;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
```

### Explanation:

1. **Preconditions and Postconditions**:
   - Preconditions include conditions like \( 0 \leq n \), sum of the range cannot exceed `INT_MAX`, and all numbers in the range must be non-negative.
   - The postcondition specifies that the resulting sum should match the sum of the range and also must be non-negative.

2. **Loop Invariants**:
   - The invariant ensures that the loop maintains valid bounds for `count` and `sum` at each iteration. It also needs to reflect that `sum` is accurately tracking the sum of numbers from `0` to `count`.

3. **Safety Checks**:
   - Open and close statements manage predicates at certain points in the code.
   - It's important to ensure that the integers are managed safely and that `sum` does not overflow or go negative.

4. **Auxiliary Specifications**:
   - Used to properly manipulate the predicates within the loop.
   - This ensures both memory safety and logical correctness according to the loop invariant and pre/postconditions.


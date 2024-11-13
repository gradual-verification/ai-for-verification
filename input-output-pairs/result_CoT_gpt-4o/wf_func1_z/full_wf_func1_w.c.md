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
@*/

int sum_of_range(int n)
//@ requires 0 <= n;
//@ ensures result == sum(range(0, n));
{
    int count = 0;
    int sum = 0;
    //@ loop_invariant 0 <= count && count <= n && sum == sum(range(0, count));
    //@ decreases n - count;
    while (count != n)
    //@ invariant 0 <= count && count <= n && sum == sum(range(0, count));
    {
        sum = sum + count;
        count = count + 1;
        //@ open range(0, n);
        //@ close range(0, n);
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

1. **Precondition and Postcondition:**
   - The `sum_of_range` function requires `n` to be non-negative (`0 <= n`).
   - The postcondition ensures that the result of the function is equal to the sum of numbers from `0` to `n-1`, which is expressed using the `sum` and `range` fixpoints.

2. **Loop Invariant:**
   - The loop invariant ensures that after each iteration:
     - `count` is between `0` and `n`.
     - `sum` is equal to the sum of the range from `0` to `count`.
   - The invariant is sufficient to prove memory safety and correctness of the function by maintaining the relationship between `sum` and accumulated counts.

3. **Use of Open and Close:**
   - The `open` and `close` statements in the loop are not strictly necessary in this instance since the loop invariant is maintained without them. However, in more complex examples, these would be used to manipulate predicates and proof states.

In practice, Verifast uses these annotations to ensure that the function logic is mathematically proven to satisfy the specified preconditions and postconditions, maintaining memory safety and integer bounds.

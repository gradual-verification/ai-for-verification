/*@
  // Predicate indicating the validity of `sum_of_range`.
  requires 0 <= n;
  // Ensures the result is the sum of the first n non-negative integers.
  ensures \result == n * (n - 1) / 2;
@*/
int sum_of_range(int n)
{
    int count = 0;
    int sum = 0;
    /*@
        // Invariant for the loop.
        loop_invariant 0 <= count <= n;
        loop_invariant sum == count * (count - 1) / 2;
        // Preserves the heap and the validity of involved variables.
        // Memory cannot change as no heap allocations are involved.
    @*/
    while (count != n)
    {
        sum = sum + count;
        count = count + 1;
    }
    return sum;
}

int main()
{
    return 0;
}

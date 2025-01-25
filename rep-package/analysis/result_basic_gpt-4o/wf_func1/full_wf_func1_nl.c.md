```c
/*
 * Verifast annotations and C code for sum_of_range function
 */

/*@
  requires n >= 0;
  ensures result == (n * (n - 1)) / 2;
@*/
int sum_of_range(int n)
{
    int count = 0;
    int sum = 0;
    /*@
      // Loop invariant to verify correctness of the loop
      loop_invariant 0 <= count <= n;
      loop_invariant sum == (count * (count-1)) / 2;
      decreases n - count;
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
```

### Explanation

- **Precondition** (`requires n >= 0;`): The function requires that `n` is a non-negative integer. This is consistent with the function’s description.
- **Postcondition** (`ensures result == (n * (n - 1)) / 2;`): This formula is derived from the arithmetic sum formula for a range from 0 to n-1. 

- **Loop Invariant**:
  - The first part (`0 <= count <= n;`) ensures that `count` is within a valid range throughout the loop.
  - The second part (`sum == (count * (count-1)) / 2;`) maintains that the sum calculated so far matches the arithmetic series sum formula, validating the incremental steps in the loop. 
  - `decreases n - count;` specifies that the distance to loop termination decreases with each iteration, ensuring the loop eventually terminates.

By including these annotations, the code can be formally verified using tools like VeriFast, which check that the code adheres to these specified behaviors.

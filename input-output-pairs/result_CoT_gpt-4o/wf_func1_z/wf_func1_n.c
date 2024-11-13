/*@
  // Predicate representing an integer range from 0 to n-1
  predicate range(int n;) =
    0 <= n;

  // Precondition: n must be non-negative
  requires range(n);
  // Postcondition: result is the sum of all numbers from 0 to n-1
  ensures result == n * (n - 1) / 2;

@*/
int sum_of_range(int n)
{
    int count = 0;
    int sum = 0;
    /*@
      // Loop invariant: 
      // 1. 0 <= count <= n - Invariant that count stays within valid bounds
      // 2. sum == count * (count - 1) / 2 - Correctness condition (sum matches the expected sum of integers up to count-1)
      loop_invariant 0 <= count <= n;
      loop_invariant sum == count * (count - 1) / 2;
      // Ensures sum doesn't exceed integer limits
      ensures sum <= n * (n - 1) / 2;
    @*/
    while (count != n)
    {
        //@ open range(n);
        sum = sum + count;
        count = count + 1;
        //@ close range(n);
    }
    return sum;
}

int main()
{
    //@ open range(0);
    return 0;
    //@ close range(0);
}

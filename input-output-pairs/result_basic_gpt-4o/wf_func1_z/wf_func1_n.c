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

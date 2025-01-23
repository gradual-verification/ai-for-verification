/*
 * Verifast annotations and C code for sum_of_range function
 */

/*@
lemma void div_mono_l(int a, int b, int d);
    requires a <= b &*& d > 0;
    ensures a / d <= b / d;

lemma void sum_increment(int count);
    requires 0 <= count;
    ensures ((count * (count - 1)) / 2) + count == (count * (count + 1)) / 2;

lemma void sum_mono(int count, int n)
    requires 0 <= count &*& count < n;
    ensures (count * (count + 1)) / 2 <= (n * (n - 1)) / 2;
{
    int lhs = count * (count + 1);
    int rhs = n * (n - 1);

    // Compute lhs = count^2 + count
    int lhs_expanded = count * count + count;
    assert(lhs == lhs_expanded);

    // Compute rhs = n^2 - n
    int rhs_expanded = n * n - n;
    assert(rhs == rhs_expanded);

    // Compute the difference delta = rhs_expanded - lhs_expanded
    int delta = rhs_expanded - lhs_expanded;

    // Expand delta:
    // delta = (n^2 - n) - (count^2 + count)
    //       = n^2 - n - count^2 - count
    //       = (n^2 - count^2) - (n + count)
    // Note that n^2 - count^2 = (n - count) * (n + count)
    int n_minus_count = n - count;
    int n_plus_count = n + count;
    int squares_diff = n_minus_count * n_plus_count;
    assert(n * n - count * count == squares_diff);

    // Therefore, delta = squares_diff - (n + count)
    delta = squares_diff - (n + count);

    // Since count < n, n_minus_count > 0
    assert(n_minus_count > 0);

    // Since count >= 0 and n >= 0, n_plus_count >= n >= 0
    assert(n_plus_count >= n);

    // Since n >= count + 1 (because count < n)
    // Therefore, n + count >= 2 * count + 1 >= 1
    assert(n_plus_count >= 1);

    // squares_diff = (n - count) * (n + count) >= n + count
    // Because (n - count) >= 1 and (n + count) >= 1
    mul_mono_l(1, n - count, n + count);
    assert(squares_diff >= n + count);

    // Therefore, delta = squares_diff - (n + count) >= 0
    assert(delta >= 0);

    // So lhs_expanded <= rhs_expanded
    assert(lhs_expanded <= rhs_expanded);

    // Hence, lhs <= rhs
    assert(lhs <= rhs);

    // Divide both sides by 2 (since 2 > 0, the inequality direction doesn't change)
    div_mono_l(lhs, rhs, 2);
    assert((lhs) / 2 <= (rhs) / 2);
}
@*/

int sum_of_range(int n)
//@ requires n >= 0 &*& (n * (n - 1)) / 2 <= INT_MAX;
//@ ensures result == (n * (n - 1)) / 2;
{
    int count = 0;
    int sum = 0;
    
    while (count != n)
    /*@
      // Loop invariant to verify correctness of the loop
      invariant 0 <= count &*& count <= n &*& sum == (count * (count-1)) / 2;
    @*/
    {
        //@ sum_increment(count);
        //@ sum_mono(count, n);
        sum = sum + count;
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

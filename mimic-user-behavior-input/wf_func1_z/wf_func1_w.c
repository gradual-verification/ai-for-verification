

int sum_of_range(int n)
//@ requires 0 <= n;
//@ ensures result == sum(range(0, n));
{
    int count = 0;
    int sum = 0;
    while (count != n)
    //@ requires 0 <= count && count <= n;
    //@ ensures sum == old_sum + sum(range(old_count, n));
    //@ decreases n - count;
    {
        sum = sum + count;
        count = count + 1;
    }
    return sum;
}

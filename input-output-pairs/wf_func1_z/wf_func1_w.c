

int sum_of_range(int n)
//@ requires 0 <= n;
//@ ensures result == sum(range(0, n));
{
    int count = 0;
    int sum = 0;
    while (count != n)
    {
        sum = sum + count;
        count = count + 1;
    }
    return sum;
}

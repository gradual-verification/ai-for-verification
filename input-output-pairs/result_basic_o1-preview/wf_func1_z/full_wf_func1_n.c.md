```c
/*@
fixpoint int sum_n(int n) {
    return n <= 0 ? 0 : sum_n(n - 1) + (n - 1);
}

requires n >= 0;
ensures result == sum_n(n);
@*/
int sum_of_range(int n)
{
    int count = 0;
    int sum = 0;
    /*@
    loop_invariant 0 <= count <= n;
    loop_invariant sum == sum_n(count);
    decreases n - count;
    @*/
    while (count != n)
    {
        sum = sum + count;
        count = count + 1;
    }
    //@ assert count == n;
    //@ assert sum == sum_n(n);
    return sum;
}

int main()
{
    return 0;
}
```

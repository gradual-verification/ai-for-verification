```c CODE and SPEC
/**@
predicate sum_of_range(int n; int sum) =
  0 <= n &*&
  0 <= sum &*&
  n == sum + 1;

@*/

/**@
requires
  n >= 0;
ensures
  result == sum_of_range(n);
@*/
int sum_of_range(int n)
{
    int count = 0;
    int sum = 0;
    while (count != n)
    //@ invariant sum_of_range(n - count, sum);
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

```c CODE and SPEC
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

fixpoint bool all_non_negative(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x0, xs0): return x0 >= 0 && all_non_negative(xs0);
    }
}
@*/

int sum_of_range(int n)
//@ requires 0 <= n &*& sum(range(0, n)) <= INT_MAX &*& all_non_negative(range(0, n)) == true;
//@ ensures result == sum(range(0, n));
{
    int count = 0;
    int sum = 0;
    /*@
    loop invariant 0 <= count <= n;
    loop invariant sum == sum(range(0, count));
    loop assigns count, sum;
    loop variant n - count;
    */
    while (count != n)
    {
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
```

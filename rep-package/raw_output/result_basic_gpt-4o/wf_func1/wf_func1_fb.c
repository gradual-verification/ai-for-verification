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
@*/

int sum_of_range(int n)
//@ requires 0 <= n;
//@ ensures result == sum(range(0, n));
{
    int count = 0;
    int sum = 0;
    //@ close exists(nil);
    //@ close exists(0);
    while (count != n)
    //@ invariant 0 <= count <= n &*& sum == sum(range(0, count));
    {
        //@ assert 0 <= count < n;
        sum = sum + count;
        count = count + 1;
        //@ close exists(range(0, count));
    }
    //@ assert count == n;
    return sum;
}

int main()
//@ requires true;
//@ ensures true;
{
    int result = sum_of_range(5);
    //@ assert result == 10;
    return 0;
}

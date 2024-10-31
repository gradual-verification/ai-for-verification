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
//@ requires 0 <= n &*& sum(range(0, n)) <= INT_MAX;
//@ ensures result == sum(range(0, n));
{
    int count = 0;
    int sum = 0;
    /*@
    loop_invariant 0 <= count <= n &*&
                   sum == sum(range(0, count)) &*&
                   sum <= sum(range(0, n)) &*&
                   sum <= INT_MAX;
    loop_variant n - count;
    @*/
    while (count != n)
    {
        //@ assert count < n;
        //@ assert sum == sum(range(0, count));
        //@ assert sum + count == sum(range(0, count + 1));
        //@ assert sum + count <= sum(range(0, n)); // Since sum(range(0, count + 1)) <= sum(range(0, n))
        sum = sum + count;
        //@ assert sum == sum(range(0, count + 1));
        count = count + 1;
        //@ assert 0 <= count <= n;
    }
    //@ assert count == n;
    //@ assert sum == sum(range(0, n));
    return sum;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

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
    //@ close range(n, n) == nil;
    //@ close all_non_negative(range(n, n)) == true;
    //@ assert sum(range(0, 0)) == 0;
    while (count != n)
    //@ invariant 0 <= count &*& count <= n &*& sum == sum(range(0, count)) &*& sum(range(0, count)) <= INT_MAX;
    {
        sum = sum + count;
        count = count + 1;
        //@ assert all_non_negative(cons(count, range(count + 1, n))) == (count >= 0 && all_non_negative(range(count + 1, n)));
    }
    //@ assert sum(range(0, n)) <= INT_MAX;
    return sum;
}

int main()
//@ requires true;
//@ ensures true;
{
    int result = sum_of_range(5);
    return 0;
}

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
//@ ensures result == sum(range(0, n)) &*& result >= 0;
{
    int count = 0;
    int sum = 0;
    //@ close all_non_negative(range(0, 0)); // Base case
    while (count != n)
    //@ invariant 0 <= count &*& count <= n &*& sum == sum(range(0, count)) &*& sum >= 0;
    {
        //@ open all_non_negative(range(0, count + 1)); // unfold the range fixedpoint
        //@ assert all_non_negative(cons(count, range(0, count)));
        sum = sum + count;
        //@ mul_nonneg_le(count, count, n); // show safe memory operations
        //@ open all_non_negative(range(0, n)); // assert non-negative
        //@ assert all_non_negative(cons(count, range(0, count)));
        //@ close all_non_negative(range(0, count + 1)); // fold back
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

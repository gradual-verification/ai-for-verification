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
    
    // Loop to calculate the sum of the range
    //@ loop_invariant 0 <= count <= n;
    //@ loop_invariant sum == sum(range(0, count));
    //@ decreases n - count;
    while (count != n)
        //@ invariant sum == sum(range(0, count));
    {
        sum = sum + count;
        //@ assert sum == sum(range(0, count + 1));
        count = count + 1;
    }

    //@ assert sum == sum(range(0, n));
    return sum;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

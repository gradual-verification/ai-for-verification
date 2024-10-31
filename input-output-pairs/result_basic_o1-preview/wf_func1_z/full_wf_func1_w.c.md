```c
/*@
fixpoint_auto list<int> range(int min, int max)
    decreases max - min;
{
    return min == max ? nil : cons(min, range(min + 1, max));
}

fixpoint int sum_list(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return x0 + sum_list(xs0);
    }
}

lemma void sum_range_extend(int min, int max)
    requires min <= max;
    ensures sum_list(range(min, max +1)) == sum_list(range(min, max)) + max;
{
    if (min > max) {
        // Base case: empty range
    } else if (min == max) {
        // Base case: single element
        // sum_list(range(min, min +1)) == min
        // sum_list(range(min, min)) == 0
        // Therefore, sum_list(range(min, min +1)) == sum_list(range(min, min)) + min
    } else {
        // Inductive step
        sum_range_extend(min +1 , max);
        // By the inductive hypothesis:
        // sum_list(range(min +1, max +1)) == sum_list(range(min +1, max)) + max
        // Therefore:
        // sum_list(range(min, max +1)) == min + sum_list(range(min +1, max +1))
        //                             == min + sum_list(range(min +1, max)) + max
        //                             == (min + sum_list(range(min +1, max))) + max
        //                             == sum_list(range(min, max)) + max
    }
}
@*/

int sum_of_range(int n)
//@ requires 0 <= n;
//@ ensures result == sum_list(range(0, n));
{
    int count = 0;
    int sum = 0;
    while(count != n)
    //@ invariant 0 <= count <= n;
    //@ invariant sum == sum_list(range(0, count));
    {
        //@ sum_range_extend(0, count);
        sum = sum + count;
        count = count + 1;
        //@ assert sum == sum_list(range(0, count));
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

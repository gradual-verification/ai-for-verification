#include <limits.h>

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
    //@ list<int> numbers = range(0, n);
    //@ close exists(numbers);
    //@ assert numbers == range(0, n);
    while (count != n)
    //@ invariant 0 <= count &*& count <= n &*& sum == sum(take(count, numbers)) &*& all_non_negative(drop(count, range(0, n))) == true &*& sum <= INT_MAX;
    {
        //@ assert all_non_negative(numbers) == true;
        //@ assert all_non_negative(drop(count, numbers)) == true;
        sum = sum + count;
        //@ take_plus_one(count, numbers);
        //@ assert sum == sum(take(count + 1, numbers));
        count = count + 1;
    }
    //@ drop_full(numbers);
    return sum;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

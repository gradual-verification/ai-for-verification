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
    //@ open all_non_negative(range(0, n));
    //@ assert range(0, n) == cons(?fst, ?rest);
    //@ int limit = sum(range(0, n));
    //@ all_non_negative(range(1, n));
    //@ close all_non_negative(range(0, n));
    
    while (count != n)
    //@ invariant 0 <= count <= n &*& sum == sum(range(0, count)) &*& sum(range(count, n)) + sum == limit &*& sum <= INT_MAX;
    {
        //@ open all_non_negative(range(0, n));
        //@ assert range(count, n) == cons(?next, ?remainder);
        sum = sum + count;
        //@ assert count < n;
        //@ close all_non_negative(range(0, n));
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

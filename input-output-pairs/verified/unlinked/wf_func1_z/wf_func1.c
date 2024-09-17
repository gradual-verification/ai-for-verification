#include "stdlib.h"

/*@

fixpoint_auto list<int> range(int min, int max)
    decreases max - min;
{
    return min == max ? nil : cons(min, range(min + 1, max));
}

fixpoint int get_sum(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return x0 + get_sum(xs0);
    }
}

// the lemma showing that if 0 <= start1 <= start2 <= end,
// then the sum of [start1, end) >= the sum of [start2, end)
lemma void sum_range_monotonic(int start1, int start2, int end);
    requires 0 <= start1 &*& start1 <= start2 &*& start2 <= end;
    ensures get_sum(range(start1, end)) >= get_sum(range(start2, end));
@*/

// calculate 0 + 1 + ... + n-1
int sum_of_range(int n)
//@ requires 0 < n &*& get_sum(range(0, n)) < INT_MAX;
//@ ensures result == get_sum(range(0, n));
{
    int cnt = n;
    int sum = 0;
    while (cnt > 0)
    //@ invariant 0 <= cnt &*& cnt <= n &*& sum == get_sum(range(cnt, n));
    {
        cnt = cnt - 1;
        //@ sum_range_monotonic(0, cnt, n);
        sum = sum + cnt;
    }

    return sum;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
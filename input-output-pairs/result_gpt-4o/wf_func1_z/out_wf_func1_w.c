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
    //@ list<int> values = range(0, n);
    //@ close foreach(values, true);
    //@ close foreach_take(0, values, true);
    while (count != n)
    //@ invariant 0 <= count <= n &*& sum == sum(take(count, values));
    {
        sum = sum + count;
        count = count + 1;
        //@ open foreach(_, _);
    }
    //@ open foreach(_, _);
    return sum;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

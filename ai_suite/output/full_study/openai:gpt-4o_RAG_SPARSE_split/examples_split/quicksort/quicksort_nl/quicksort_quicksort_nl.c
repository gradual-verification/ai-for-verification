#include <stdlib.h>
#include <stdio.h>

//@ #include "prelude.h"
//@ #include "list.gh"

/*@

predicate ints(int *p, int count; list<int> vs) =
    count == 0 ?
        vs == nil
    :
        integer(p, ?v) &*& ints(p + 1, count - 1, ?vs0) &*& vs == cons(v, vs0);

lemma_auto void ints_to_ints_(int *p);
    requires ints(p, ?count, ?vs);
    ensures ints_(p, count, map(some, vs));

lemma_auto void ints__to_ints(int *p);
    requires ints_(p, ?count, ?vs) &*& vs == map(some, map(the, vs));
    ensures ints(p, count, map(the, vs));

lemma_auto void ints_inv();
    requires [?f]ints(?p, ?count, ?vs);
    ensures [f]ints(p, count, vs) &*& count == length(vs);

lemma_auto void ints__inv();
    requires [?f]ints_(?p, ?count, ?vs);
    ensures [f]ints_(p, count, vs) &*& count == length(vs);

predicate malloc_block_ints(int *p; int count) = malloc_block(p, count * sizeof(int));

@*/

/*@
predicate array(int *a, int n, list<int> vs) =
    ints(a, n, vs) &*& malloc_block_ints(a, n);
@*/

void swap(int *a, int i, int j)
    //@ requires array(a, ?n, ?vs) &*& 0 <= i &*& i < n &*& 0 <= j &*& j < n;
    //@ ensures array(a, n, update(i, nth(j, vs), update(j, nth(i, vs), vs)));
{
    //@ open array(a, n, vs);
    int aj = a[j];
    a[j] = a[i];
    a[i] = aj;
    //@ close array(a, n, update(i, nth(j, vs), update(j, nth(i, vs), vs)));
}

int partition(int *a, int lo, int hi)
    //@ requires array(a, ?n, ?vs) &*& 0 <= lo &*& lo <= hi &*& hi < n;
    //@ ensures array(a, n, ?vs1) &*& 0 <= result &*& result <= hi &*&
    //@         take(result, vs1) == take(result, vs) &*&
    //@         drop(result + 1, vs1) == drop(result + 1, vs) &*&
    //@         nth(result, vs1) == nth(hi, vs) &*&
    //@         forall(take(result, vs1), (lt)(nth(hi, vs))) == true &*&
    //@         forall(drop(result + 1, vs1), (ge)(nth(hi, vs))) == true;
{
    //@ open array(a, n, vs);
    int pivot = a[hi];
    int i = lo - 1;
    int j;

    for (j = lo; j < hi; j++)
        //@ invariant array(a, n, ?vs0) &*& lo <= j &*& j <= hi &*& i < j &*& i >= lo - 1 &*&
        //@           take(i + 1, vs0) == take(i + 1, vs) &*& drop(j, vs0) == drop(j, vs) &*&
        //@           forall(take(i + 1, vs0), (lt)(pivot)) == true;
    {
        if (a[j] < pivot) {
            i++;
            swap(a, i, j);
            //@ open array(a, n, ?vs1);
            //@ assert vs1 == update(i, nth(j, vs0), update(j, nth(i, vs0), vs0));
            //@ close array(a, n, vs1);
        }
    }
    i++;
    swap(a, i, hi);
    //@ open array(a, n, ?vs2);
    //@ assert vs2 == update(i, nth(hi, vs1), update(hi, nth(i, vs1), vs1));
    //@ close array(a, n, vs2);
    return i;
}

void quicksort(int *a, int lo, int hi)
    //@ requires array(a, ?n, ?vs) &*& 0 <= lo &*& lo <= hi &*& hi < n;
    //@ ensures array(a, n, ?vs1) &*& sorted(take(hi - lo + 1, drop(lo, vs1))) == true;
{
    if (lo > hi) {
        return;
    } else {
        int p = partition(a, lo, hi);
        quicksort(a, lo, p - 1);
        quicksort(a, p + 1, hi);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    int a[5] = {3, 1, 4, 1, 5};
    //@ close array(a, 5, cons(3, cons(1, cons(4, cons(1, cons(5, nil))))));
    quicksort(a, 0, 4);
    //@ open array(a, 5, ?vs);
    //@ assert sorted(vs) == true;
    return 0;
}
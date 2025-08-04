#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

/*@
predicate array(struct int_array *arr, list<int> cs) =
    malloc_block_int_array(arr) &*&
    arr->values[..10] |-> cs;
@*/

/*@
fixpoint_auto list<int> zeros(int n) {
    return n == 0? nil : append(zeros(n - 1), cons(0, nil));
}
@*/

/*@
lemma void ints_split(int* p, int i)
    requires ints(p, ?n, ?vs) &*& 0 <= i && i <= n;
    ensures ints(p, i, take(i, vs)) &*& ints(p + i, n - i, drop(i, vs));
{
    if (i == 0) {
        close ints(p, 0, nil);
    } else {
        open ints(p, n, vs);
        ints_split(p + 1, i - 1);
        close ints(p, i, take(i, vs));
    }
}

lemma void ints_join(int* p)
    requires ints(p, ?n1, ?vs1) &*& ints(p + n1, ?n2, ?vs2);
    ensures ints(p, n1 + n2, append(vs1, vs2));
{
    if (n1 > 0) {
        open ints(p, n1, vs1);
        ints_join(p + 1);
        close ints(p, n1 + n2, append(vs1, vs2));
    }
}
@*/

void set(struct int_array *arr, int index, int value)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, update(index, value, elems));
{
    //@ open array(arr, elems);
    //@ ints_split(arr->values, index);
    //@ ints_split(arr->values + index, 1);
    arr->values[index] = value;
    //@ ints_join(arr->values + index);
    //@ ints_join(arr->values);
    //@ close array(arr, update(index, value, elems));
}
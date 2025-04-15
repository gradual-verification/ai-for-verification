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

/*@ fixpoint_auto list<int> zeros(int n) {
    return n == 0 ? nil : cons(0, zeros(n - 1));
}
@*/

void fill_zeros(int *arr, int i, int n)
    //@ requires arr[i..n] |-> _ &*& 0 <= i && i <= n;
    //@ ensures arr[i..n] |-> zeros(n - i);
{
    if (i == n) {
    } else {
        arr[i] = 0;
        fill_zeros(arr, i + 1, n);
    }
}

struct int_array *create_array()
    //@ requires emp;
    //@ ensures array(result, zeros(10));
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    fill_zeros(arr->values, 0, 10);
    return arr;
}

void set(struct int_array *arr, int index, int value)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, update(index, value, elems));
{
    arr->values[index] = value;
}

int get(struct int_array *arr, int index)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, elems) &*& result == nth(index, elems);
{
    return arr->values[index];
}

void dispose_array(struct int_array *arr)
    //@ requires array(arr, _);
    //@ ensures emp;
{
    free(arr);
}

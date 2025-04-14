#include <stdlib.h>
#include <stdbool.h>

#define SIZE 10

struct int_array {
    int values[SIZE];
};

/*@
predicate array(struct int_array *arr, list<int> cs) =
    malloc_block_int_array(arr) &*&
    arr->values[..SIZE] |-> cs;
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

// Create a new array initialized with zeros
struct int_array *create_array()
    //@ requires true;
    //@ ensures array(result, zeros(SIZE));
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    fill_zeros(arr->values, 0, SIZE);
    //@ close array(arr, zeros(SIZE));
    return arr;
}

// Set the value at index
void set(struct int_array *arr, int index, int value)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < SIZE;
    //@ ensures array(arr, update(index, value, elems));
{
    //@ open array(arr, elems);
    arr->values[index] = value;
    //@ close array(arr, update(index, value, elems));
}

// Get the value at index
int get(struct int_array *arr, int index)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < SIZE;
    //@ ensures array(arr, elems) &*& result == nth(index, elems);
{
    //@ open array(arr, elems);
    return arr->values[index];
    //@ close array(arr, elems);
}

// Dispose of the array
void dispose_array(struct int_array *arr)
    //@ requires array(arr, _);
    //@ ensures true;
{
    //@ open array(arr, _);
    free(arr);
}

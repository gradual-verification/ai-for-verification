#include <stdlib.h>
#include <stdbool.h>

struct int_array {
    int values[10];
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `set` function sets the element at the given index in an int_array to be the given value.
 * 
 * @param arr: the int_array to be set
 * @param index: the index to be set into, which is >= 0 and < 10
 * @param value: the value to be set with
 * 
 * It makes sure that the new int_array is updated with the value. 
 */
/*@ 
predicate int_array(struct int_array *arr, list<int> values) =
    arr->values |-> ?vs &*& length(vs) == 10 &*& ints(vs, 10, values);

lemma_auto void ints_to_ints_(int *p);
    requires ints(p, ?count, ?vs);
    ensures ints_(p, count, map(some, vs));

lemma_auto void ints__to_ints(int *p);
    requires ints_(p, ?count, ?vs) &*& vs == map(some, map(the, vs));
    ensures ints(p, count, map(the, vs));

@*/
void set(struct int_array *arr, int index, int value)
    //@ requires int_array(arr, ?values) &*& 0 <= index &*& index < 10;
    //@ ensures int_array(arr, update(index, value, values));
{
    //@ open int_array(arr, values);
    arr->values[index] = value;
    //@ close int_array(arr, update(index, value, values));
}
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

// TODO: make this function pass the verification
void set(struct int_array *arr, int index, int value)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, update(index, value, elems));
{
    arr->values[index] = value;
}

/*@
fixpoint list<int> update(int index, int value, list<int> elems) {
    return index == 0 ? cons(value, tail(elems)) : cons(head(elems), update(index - 1, value, tail(elems)));
}
@*/

/*@
lemma void update_length(list<int> elems, int index, int value)
    requires true;
    ensures length(update(index, value, elems)) == length(elems);
{
    switch(elems) {
        case nil:
        case cons(h, t):
            if(index == 0) {
            } else {
                update_length(t, index - 1, value);
            }
    }
}
@*/

/*@
lemma void update_array(struct int_array *arr, int index, int value, list<int> elems)
    requires array(arr, elems) &*& 0 <= index &*& index < 10;
    ensures array(arr, update(index, value, elems));
{
    open array(arr, elems);
    arr->values[index] = value;
    close array(arr, update(index, value, elems));
}
@*/
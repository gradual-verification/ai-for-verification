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
  return n ==0? nil : append(zeros(n -1), cons(0, nil));
}
@*/

// TODO: make this function pass the verification
int get(struct int_array *arr, int index)
  //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
  //@ ensures array(arr, elems) &*& result == nth(index, elems);
{
  return arr->values[index];
}
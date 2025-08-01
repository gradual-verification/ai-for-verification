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
lemma void ints_join(int *p, int n, list<int> vs, int n0, list<int> vs0)
  requires [?f]ints(p, n, vs) &*& [f]ints(p + n, n0, vs0);
  ensures  [f]ints(p, n + n0, append(vs, vs0));
{
  open ints(p, n, vs);
  switch(vs) {
    case nil:
      return;
    case cons(v, vsTail):
      ints_join(p + 1, n - 1, vsTail, n0, vs0);
      return;
  }
}
@*/

struct int_array *create_array()
    //@ requires true;
    //@ ensures array(result, zeros(10));
{
    struct int_array *arr = malloc(sizeof(struct int_array));
    if (!arr) abort();
    int *values = arr->values;

    // @ close ints(values, 0, zeros(0));
    // @ close ints(values, 10, _);
    for (int i = 0; i < 10; i++)
        /*@
          invariant
            0 <= i && i <= 10
          &*& ints(values, i, zeros(i))
          &*& ints_(values + i, 10 - i, _);
        @*/
    {
        values[i] = 0;
        //@ ints_join(values, i, zeros(i), 1, zeros(1));
    }

    //@ close array(arr, zeros(10));
    return arr;
}

void set(struct int_array *arr, int index, int value)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, update(index, value, elems));
{
    //@ open array(arr, elems);
    arr->values[index] = value;
    //@ close array(arr, update(index, value, elems));
}

int get(struct int_array *arr, int index)
    //@ requires array(arr, ?elems) &*& 0 <= index && index < 10;
    //@ ensures array(arr, elems) &*& result == nth(index, elems);
{
    //@ open array(arr, elems);
    return arr->values[index];
    //@ close array(arr, elems);
}

void dispose_array(struct int_array *arr)
    //@ requires array(arr, _);
    //@ ensures true;
{
    //@ open array(arr, _);
    free(arr);
}

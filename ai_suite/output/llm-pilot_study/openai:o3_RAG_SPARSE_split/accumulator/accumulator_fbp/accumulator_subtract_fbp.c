#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*&
  a->count |-> c &*&
  malloc_block_Accumulator(a);
@*/

/*  subtract
    Decrease the accumulator’s total by x and increase the counter.
*/
void subtract(struct Accumulator* a, int x)
  /*@
  requires
      Accumulator(a, ?t, ?c) &*&
      t - x <= INT_MAX &*&                // no signed-integer under/overflow
      t - x >= INT_MIN &*&
      c < INT_MAX;                       // room for the increment
  ensures
      Accumulator(a, t - x, c + 1);
  @*/
{
  /*@ open Accumulator(a, t, c); @*/

  /* read and check current total                                        */
  int total = a->total;
  //@ assert total == t;
  //@ produce_limits(total);            // total   ∈ [INT_MIN,INT_MAX]
  //@ produce_limits(x);               // x       ∈ [INT_MIN,INT_MAX]

  int newTotal = total - x;            // safe: pre-condition guarantees range

  /* read and check current counter                                      */
  int count = a->count;
  //@ assert count == c;
  //@ produce_limits(count);            // count   ∈ [INT_MIN,INT_MAX]

  int newCount = count + 1;            // safe:    c < INT_MAX

  /* write back the updated fields                                       */
  a->total = newTotal;
  a->count  = newCount;

  /*@ close Accumulator(a, newTotal, newCount); @*/
}
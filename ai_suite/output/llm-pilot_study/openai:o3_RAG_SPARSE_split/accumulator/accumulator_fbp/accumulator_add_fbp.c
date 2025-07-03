#include "stdlib.h"

/*  A very small “library” : an integer accumulator.
    The single function below (‘add’) is the one that was marked
    “// TODO: make this function pass the verification”.
    The body has been rewritten and annotated so that VeriFast
    can prove the contract that is given in the header.          */

struct Accumulator {
  int total;
  int count;
};

/*@  The state of an Accumulator consists of the two
     integer fields and the malloc-block that owns the
     memory of the structure.                                      */
predicate Accumulator(struct Accumulator *a, int t, int c) =
  a->total |-> t &*&
  a->count |-> c &*&
  malloc_block_Accumulator(a);

/*  ------------------------------------------------------------
    Verified implementation
    ------------------------------------------------------------ */

/*  Adds the value ‘x’ to the running total and increases the
    counter.  The caller must guarantee that both additions fit
    in the ‘int’ range; the post-condition states the new logical
    content of the accumulator.                                   */
void add(struct Accumulator* a, int x)
  /*@ requires
        Accumulator(a, ?t, ?c) &*&                // current state
        INT_MIN <= t + x &*&                      // no overflow
        t      <= INT_MAX - x &*&
        c < INT_MAX;                              // room for +1
      @*/
  /*@ ensures
        Accumulator(a, t + x, c + 1);             // updated state
      @*/
{
  /*------------------------------------------------------------
    Unpack the predicate so we get access to the two field chunks
    (and the logical values t and c).
    ------------------------------------------------------------*/
  //@ open Accumulator(a, t, c);

  /*  1.  Update the ‘total’ field.  We store the old value in a
          local variable so that we can refer to it in assertions.   */
  int old_total = a->total;
  //@ produce_limits(old_total);
  //@ assert old_total == t;                      // by definition
  int new_total = old_total + x;
  /*  The pre-condition provides exactly the two inequalities
      below, so VeriFast can prove them automatically.             */
  //@ assert INT_MIN <= new_total;
  //@ assert new_total <= INT_MAX;
  a->total = new_total;                           // write back

  /*  2.  Update the ‘count’ field, analogously.                     */
  int old_count = a->count;
  //@ produce_limits(old_count);
  //@ assert old_count == c;
  int new_count = old_count + 1;
  //@ assert new_count == c + 1;
  //@ assert new_count <= INT_MAX;                // because c < INT_MAX
  a->count = new_count;

  /*------------------------------------------------------------
    Re-assemble the predicate with the updated logical values.
    ------------------------------------------------------------*/
  //@ close Accumulator(a, new_total, new_count);
}
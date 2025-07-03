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

/*  Verified function */
void add_multiple(struct Accumulator* a, int n, int x)
/*@
  requires Accumulator(a, ?t, ?c)
           &*& n >= 1
           &*& x >= 0
           &*& t + n * x <= INT_MAX
           &*& c + n     <= INT_MAX;
@*/
/*@
  ensures  Accumulator(a, t + n * x, c + n);
@*/
{
    //@ open Accumulator(a, t, c);

    int i = 0;

    while (i < n)
        /*@
        invariant
              0 <= i &*& i <= n
           &*& a->total |-> t + i * x
           &*& a->count |-> c + i
           &*& malloc_block_Accumulator(a)
           &*& x >= 0
           &*& t + n * x <= INT_MAX
           &*& t + i * x <= INT_MAX
           &*& c + i     <= INT_MAX;
        decreases n - i;
        @*/
    {
        /* update the fields */
        a->total += x;
        a->count += 1;

        i++;

        //@ mul_mono_l(i, n, x);                /* i*x <= n*x          */
        //@ assert t + i * x <= INT_MAX;        /* still within range  */
        //@ assert c + i     <= INT_MAX;        /* still within range  */
    }

    //@ assert i == n;                          /* loop exited at n    */
    //@ close Accumulator(a, t + n * x, c + n);
}
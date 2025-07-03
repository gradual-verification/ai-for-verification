#include "stdlib.h"

/*  
   A heap-allocated Accumulator object consists of two
   integer fields (total and count) and the malloc block that
   contains them.
*/

/*@
predicate malloc_block_Accumulator(struct Accumulator *p) =
  malloc_block(p, sizeof(struct Accumulator));
@*/

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator *a, int t, int c) =
  a->total |-> t &*&
  a->count |-> c &*&
  malloc_block_Accumulator(a);
@*/

/* Constructor */

/*@
requires  true;
ensures   Accumulator(result, v, 1);
@*/
struct Accumulator *create(int v)
//@ terminates;
{
  struct Accumulator *a = malloc(sizeof(struct Accumulator));
  if (a == 0) {
    abort();                        /* never returns */
  }

  /* initialise the freshly allocated structure */
  a->total = v;
  a->count = 1;

  /* establish the predicate for the caller */
  //@ close Accumulator(a, v, 1);
  return a;
}
predicate_family_instance thread_run_pre(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);
predicate_family_instance thread_run_post(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);
// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.h"
#include "threading.h"

static int cell;

/*@

predicate_family_instance thread_run_pre(m)(void *data, real frac) = ticket(integer, &cell, frac) &*& [frac]integer(&cell, _);
predicate_family_instance thread_run_post(m)(void *data, real frac) = ticket(integer, &cell, frac) &*& [frac]integer(&cell, _);

predicate thread_info(struct thread *t) = thread(t, m, _, _);

@*/


void m(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(m)(data, ?frac);
    //@ ensures thread_run_post(m)(data, frac);
{
    int x = cell;
}
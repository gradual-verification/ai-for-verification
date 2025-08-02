// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.h"
#include "threading.h"

static int cell;

/*@

predicate_family_instance thread_run_pre(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& cell |-> ?x;
predicate_family_instance thread_run_post(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& cell |-> ?x;

predicate thread_info(struct thread *t) = thread(t, m, _, _);

@*/

// TODO: make this function pass the verification
void m(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(m)(data, ?info);
    //@ ensures thread_run_post(m)(data, info);
{
    //@ open thread_run_pre(m)(data, info);
    int x = cell;
    //@ close thread_run_post(m)(data, info);
}
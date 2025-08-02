#include "stdlib.h"
#include "threading.h"

// Global variable
static int cell;

//@ predicate cell_pred() = integer(&cell, _);

//@ predicate_family_instance thread_run_pre(m)(void *data, any info) = cell_pred();
//@ predicate_family_instance thread_run_post(m)(void *data, any info) = cell_pred();

// TODO: make this function pass the verification
void m(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(m)(data, ?info);
    //@ ensures thread_run_post(m)(data, info);
{
    //@ open thread_run_pre(m)(data, info);
    int x = cell;
    //@ close thread_run_post(m)(data, info);
}
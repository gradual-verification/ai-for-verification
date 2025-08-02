// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.h"
#include "threading.h"

static int cell;

//@ predicate_family_instance thread_run_pre(m)(void *data, any info) = emp;
//@ predicate_family_instance thread_run_post(m)(void *data, any info) = emp;

// TODO: make this function pass the verification
/*m function
- param data: pointer to data
- description: reads the value of the global variable cell, making sure that the data is not changed. 
*/
void m(void *data) //@ : thread_run_joinable
//@ requires thread_run_pre(m)(data, ?info);
//@ ensures thread_run_post(m)(data, info);
{
    //@ open thread_run_pre(m)(data, info);
    
    // Create a local variable to store the value of cell
    int x = cell;
    
    //@ close thread_run_post(m)(data, info);
}
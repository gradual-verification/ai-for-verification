// Includes necessary libraries
//@ #include "counting.gh"
#include "stdlib.h"
#include "threading.h"

static int cell;


// TODO: make this function pass the verification
/*m function
- param data: pointer to data
- description: reads the value of the global variable cell, making sure that the data is not changed. 
*/
void m(void *data) //@ : thread_run_joinable
{
    int x = cell;
}


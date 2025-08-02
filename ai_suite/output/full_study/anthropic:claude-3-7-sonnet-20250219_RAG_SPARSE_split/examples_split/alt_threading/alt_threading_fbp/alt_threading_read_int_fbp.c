#include "stdlib.h"

struct thread;

//@ predicate thread(struct thread *thread, predicate() post);

//@ predicate_ctor integer1(int *cell, int value)(int *cell1) = integer(cell, value) &*& cell1 == cell;
//@ predicate_ctor integer2(int *cell, int value)() = integer(cell, value);

int read_int()
    //@ requires true;
    //@ ensures true;
{
    int *value = malloc(sizeof(int));
    if (value == 0) abort();
    *value = 0; // Initialize with a default value
    
    // We can use the value and then free it
    int result = *value;
    free(value);
    
    return result;
}
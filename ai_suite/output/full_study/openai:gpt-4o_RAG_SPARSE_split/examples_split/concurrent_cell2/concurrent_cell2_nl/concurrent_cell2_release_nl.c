#include "prelude.h"

// atomic_dec function
// -param: c: pointer to the cell
// -description: atomically decrement the value of the cell. 
//
// It doesn't have any implementation.
//
// It requires that the decrement operation is allowed on the cell.
// It ensures that this decrement operation must finish at the end 
// (while operations of other threads can be finished concurrently during this operation),
// so the old trace is the prefix of current trace.
void atomic_dec(int* c);

// TODO: make this function pass the verification
// release function
// -param: c: pointer to the cell
// -description: release the lock by decrementing the value of c
//
// It requires that the lock of old trace is held by the current thread,
// and it ensures that the lock of the new trace is not held by no thread. 
void release(int* c)
    //@ requires integer(c, ?v) &*& v > 0;
    //@ ensures integer(c, v - 1);
{
    atomic_dec(c);
}
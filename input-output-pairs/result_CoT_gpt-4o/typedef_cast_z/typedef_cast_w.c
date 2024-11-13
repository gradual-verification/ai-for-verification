#include <stdint.h>

typedef short my_short;

// Predicate to represent the state of variable
// These are simple without loop, so memory safety checks are simple here.

// Function `foo` verifies behavior based on 16-bit integer operations and valid pointer usage.
void foo(int16_t x, my_short y)
    //@ requires INT16_MIN <= x <= INT16_MAX &*& INT16_MIN <= y <= INT16_MAX;
    //@ ensures true;
{
    // Calculation using safe 16-bit integer arithmetic
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    
    my_short *pz = &z;
    // Ensures valid upcasting to void* and back to original type
    void *pv = pz;
    //@ open &z |-> _;
    pz = (my_short *)pv;
    //@ close &z |-> _;
    
    // No dynamic memory is involved, and no loops are present, 
    // so no additional loop invariants or memory leak checks required.
}

int main()
    //@ requires true;
    //@ ensures true;
{
    // Main function doesn't perform relevant operations for memory safety checks,
    // so standard true precondition and postcondition suffice.
    return 0;
}

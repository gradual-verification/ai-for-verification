#include <stdint.h>
#include <limits.h>

typedef short my_short;

void foo(int16_t x, my_short y)
//@ requires x - y >= SHRT_MIN &*& x - y <= SHRT_MAX;
//@ ensures true;
{
    int16_t diff = (int16_t)(x - y);
    //@ assert diff == x - y; // Ensure the calculation is correct and within bounds
    my_short z = (my_short)diff;
    //@ assert z == x - y; // Safe to cast as ensured by precondition
    my_short *pz = &z;
    void *pv = pz;
    //@ assert pv == (void *)&z; // Ensure the pointer conversion is safe and correct
    pz = (my_short *)pv;
    //@ assert pz == &z; // Ensure the types are correctly restored and point to the same memory
}

int main()
//@ requires true;
//@ ensures true;
{
    foo(INT16_MAX, 0);  // Example call to foo to demonstrate usage
    return 0;
}

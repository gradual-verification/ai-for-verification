#include <stdint.h>
#include <limits.h>

typedef short my_short;

void foo(int16_t x, my_short y)
//@ requires x - y >= SHRT_MIN &*& x - y <= SHRT_MAX;
//@ ensures true;
{
    my_short z = (my_short)(x - y);
    //@ assert z == (x - y); // Assert that z holds the result of x - y within the bounded range
    z = (int16_t)(x - y);
    //@ assert z == (x - y); // Reassert the same because casting to int16_t should not change the value
    my_short *pz = &z;
    //@ assert *pz == z; // Assert that pz points to z and holds the same value
    void *pv = pz;
    //@ assert (my_short *)pv == pz; // Assert that casting back to my_short* yields the same pointer
    pz = (my_short *)pv;
    //@ assert *pz == z; // Assert that dereferencing pz gives the correct value of z
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

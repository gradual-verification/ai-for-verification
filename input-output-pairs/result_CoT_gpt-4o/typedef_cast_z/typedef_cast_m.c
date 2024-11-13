#include <stdint.h>
#include <limits.h>

typedef short my_short;

void foo(int16_t x, my_short y)
//@ requires x - y >= SHRT_MIN &*& x - y <= SHRT_MAX;
//@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z; // z is already declared and initialized, pointing to it is valid
    void *pv = pz;     // Valid conversion from my_short* to void*
    pz = (my_short *)pv; // Valid cast back from void* to my_short*
    //@ assert *pz == (my_short)(x - y);
}

int main()
//@ requires true;
//@ ensures true;
{
    //@ open exists(true);
    return 0;
}

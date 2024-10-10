#include <stdint.h>

typedef short my_short;

void foo(int16_t x, my_short y)
//@ requires true;
//@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (my_short)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;

    //@ assert sizeof(my_short) == sizeof(short);
    //@ assert (uintptr_t)pz == (uintptr_t)&z;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

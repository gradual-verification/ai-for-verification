#include <stdint.h>

typedef short my_short;

void foo(int16_t x, my_short y)
//@ requires true;
//@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    //@ assert pointer(pz, z);
    void *pv = pz;
    //@ assert pointer((my_short *)pv, z);
    pz = (my_short *)pv;
    //@ assert pointer(pz, z);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

#include <stdint.h>

typedef short my_short;

void foo(int16_t x, my_short y)
    //@ requires x - y >= -32768 &*& x - y <= 32767;
    //@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
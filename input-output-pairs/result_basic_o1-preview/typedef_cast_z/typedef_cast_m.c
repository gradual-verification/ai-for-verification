#include <stdint.h>
#include <limits.h>

typedef short my_short;

void foo(int16_t x, my_short y)
 //@ requires x - y >= SHRT_MIN &*& x - y <= SHRT_MAX;
 //@ ensures true;
{
    my_short z = (my_short)(x - y);
    //@ assert z == x - y;
    z = (int16_t)(x - y);
    //@ assert z == x - y;
    my_short *pz = &z;
    //@ assert pz == &z;
    void *pv = pz;
    pz = (my_short *)pv;
    //@ assert pz == &z;
}

int main()
 //@ requires true;
 //@ ensures true;
{
    return 0;
}

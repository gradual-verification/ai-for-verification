#include <stdint.h>

typedef short my_short;


void foo(int16_t x, my_short y)
    //@ requires INT16_MIN <= x &*& x <= INT16_MAX &*& SHRT_MIN <= y &*& y <= SHRT_MAX &*& x - y >= SHRT_MIN &*& x - y <= SHRT_MAX;
    //@ ensures true;
{
    my_short z = (my_short)(x - y);
    //@ assert SHRT_MIN <= z && z <= SHRT_MAX;
    
    z = (int16_t)(x - y);
    //@ assert SHRT_MIN <= z && z <= SHRT_MAX;

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

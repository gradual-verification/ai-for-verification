#include <stdint.h>
#include <limits.h>

typedef short my_short;

// Function foo
void foo(int16_t x, my_short y)
    /*@ 
    requires x - y >= SHRT_MIN &*& x - y <= SHRT_MAX;
    ensures true;
    @*/
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
}

// Main function
int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}

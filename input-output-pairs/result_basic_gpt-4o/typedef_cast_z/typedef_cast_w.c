#include <stdint.h>

typedef short my_short;

void foo(int16_t x, my_short y)
//@ requires true;
//@ ensures true;
{
    my_short z = (my_short)(x - y); // Narrowing the integer subtraction to my_short
    z = (int16_t)(x - y); // Explicit cast, even though it's unnecessary, maintains the data type consistency
    my_short *pz = &z; // Taking the address of z
    void *pv = (void *)pz; // Casting my_short* to void*
    pz = (my_short *)pv; // Casting back void* to my_short*

    /* VeriFast will ensure that these pointer cast operations are safe.
       Since we do not modify what pz points to via pv here, no aliasing issues arise.
       All these casts are safe because they don't violate alignment requirements
       or type safety. */
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

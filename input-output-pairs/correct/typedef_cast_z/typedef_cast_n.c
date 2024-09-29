#include <stdint.h>

typedef short my_short;

/*** 
 * Description: This function performs type casting operations on integer values, 
showcasing the conversion between int16_t and a user-defined type my_short.

@param x - An integer of type int16_t.
@param y - An integer of type my_short. Note that x - y should be within the range of short type.
*/
void foo(int16_t x, my_short y)
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
#include <stdint.h>

typedef short my_short;

void foo(int16_t x, my_short y)
//@ requires true;
//@ ensures true;
{
    my_short z = (my_short)(x - y);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

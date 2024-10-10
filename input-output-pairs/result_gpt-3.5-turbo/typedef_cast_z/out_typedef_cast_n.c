
#include <stdint.h>

typedef short my_short;

/*@

// Predicate for specifying the relationship between int16_t and my_short
predicate my_short_relation(int16_t x, my_short y) = y == (my_short)x;

// Specification for the foo function
requires my_short_relation(x, y);
ensures my_short_relation(x, \result);
ensures \result == (my_short)(x - y);
void foo(int16_t x, my_short y)
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
}

int main()
{
    return 0;
}

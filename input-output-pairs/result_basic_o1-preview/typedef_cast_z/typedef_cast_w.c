#include <stdint.h>
#include <stdlib.h>

/*@

typedef short my_short;

@*/

void foo(int16_t x, my_short y)
    //@ requires true;
    //@ ensures true;
{
    my_short *pz = malloc(sizeof(my_short));
    if (pz == 0) { abort(); }
    //@ malloc_block(pz, sizeof(my_short));
    //@ chars_to_shorts(pz, 1);

    *pz = (my_short)(x - y);
    *pz = (int16_t)(x - y);
    void *pv = pz;
    pz = (my_short *)pv;

    //@ shorts_to_chars(pz, 1);
    //@ open malloc_block(pz, sizeof(my_short));
    free(pz);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    foo(1, 2);
    return 0;
}

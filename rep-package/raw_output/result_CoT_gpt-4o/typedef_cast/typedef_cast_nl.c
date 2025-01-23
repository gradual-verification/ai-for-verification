#include <stdint.h>
#include <limits.h>

typedef short my_short;

/*@ 
  predicate valid_int16_t(int16_t x;) = x >= INT16_MIN && x <= INT16_MAX;
  predicate valid_my_short(my_short y;) = y >= SHRT_MIN && y <= SHRT_MAX;

  /******************************************
   * Description: This function performs type casting
   * operations on integer values, showcasing the conversion
   * between int16_t and a user-defined type my_short.
   *
   * @param x - An integer of type int16_t.
   * @param y - An integer of type my_short.
   *
   * Preconditions:
   * - @predicate valid_int16_t(x);
   * - @predicate valid_my_short(y);
   *
   * Postconditions:
   * - @predicate valid_my_short(*(my_short *)pv);
   ******************************************/
@*/
void foo(int16_t x, my_short y)
//@ requires valid_int16_t(x) &*& valid_my_short(y);
//@ ensures valid_my_short(*(my_short *)(void *)&x) &*& valid_my_short(*(my_short *)(void *)&y);
{
    my_short z = (my_short)(x - y);
    //@ assert valid_my_short(z);
    z = (int16_t)(x - y);
    //@ assert valid_my_short(z);
    my_short *pz = &z;
    void *pv = pz;
    //@ assert pv == (void *)&z;
    pz = (my_short *)pv;
    //@ assert pz == (my_short *)pv;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

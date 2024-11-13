#include <stdint.h>

typedef short my_short;

/*@
predicate my_short_valid(my_short *ptr) =
    pointer(ptr, _);

predicate foo_input_bounds(int16_t x, my_short y) =
    x >= INT16_MIN && x <= INT16_MAX && 
    y >= INT16_MIN && y <= INT16_MAX;

predicate foo_output_bounds(my_short z) =
    z >= INT16_MIN && z <= INT16_MAX;
*/

/*** 
 * Description: This function performs type casting operations on integer values, 
 보여주는 정수형과 사용자 정의 타입 my_short간의 변환.
 
@param x - 정수형 인수 of type int16_t.
@param y - 정수형 인수 of type my_short.
@pre  foo_input_bounds(x, y) &*& my_short_valid(pz);
@post foo_output_bounds(z) &*& my_short_valid(pz);
*/
void foo(int16_t x, my_short y)
    //@ requires foo_input_bounds(x, y) &*& my_short_valid(?pz);
    //@ ensures foo_output_bounds(?z) &*& my_short_valid(pz);
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

#include <stdint.h>

typedef short my_short;

/*
  Natural Language Specification:
  - Description: This function performs type casting operations on integer values, showcasing the conversion between `int16_t` and a user-defined type `my_short`.
  - Parameters:
    - `x`: An integer of type `int16_t`.
    - `y`: An integer of type `my_short`.
  - Requires: No specific preconditions.
  - Ensures: The function does not return a value and serves primarily to demonstrate casting between different types.
  - Operation:
    1. Subtracts `y` from `x` and casts the result to `my_short`, storing it in variable `z`.
    2. Casts the result of `x - y` to `int16_t` and assigns it to `z`.
    3. Takes the address of `z` and stores it in a pointer `pz`.
    4. Casts the pointer `pz` to a `void *` type and stores it in `pv`.
    5. Casts `pv` back to a `my_short *` type and assigns it to `pz`.
*/
void foo(int16_t x, my_short y)
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
}

//@ #include <bitops.gh>
//@ #include <target.gh>
#include <stdint.h>
#include <assert.h>


/**
 * Function: bitand_uint8_symm_test
 *
 * This function tests the symmetry property of the bitwise AND operation for `uint8_t` values.
 *
 * Inputs:
 * - x: An unsigned 8-bit integer.
 * - y: An unsigned 8-bit integer.
 *
 * Behavior:
 * - The function asserts that the result of the bitwise AND operation between x and y is equal to the result of the bitwise AND operation between y and x.
 * - The function also asserts that the result of the bitwise AND operation between x and the constant 123 is equal to the result of the bitwise AND operation between 123 and x.
 *
 * These assertions verify the commutativity of the bitwise AND operation, ensuring that `x & y` is always equal to `y & x` and `x & 123` is always equal to `123 & x`.
 */

void bitand_uint8_symm_test(uint8_t x, uint8_t y)

{
    
    assert((x & y) == (y & x));
    
    assert((x & 123) == (123 & x));
}

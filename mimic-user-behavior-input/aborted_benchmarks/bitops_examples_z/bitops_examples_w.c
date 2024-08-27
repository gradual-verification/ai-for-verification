//@ #include <bitops.gh>
//@ #include <target.gh>
#include <stdint.h>
#include <assert.h>

void bitand_uint8_symm_test(uint8_t x, uint8_t y)
//@ requires true;
//@ ensures true;
{
   
    assert((x & y) == (y & x));
   
    assert((x & 123) == (123 & x));
}

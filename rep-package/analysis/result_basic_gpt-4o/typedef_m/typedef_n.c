#include <assert.h>

// Define typedef as per original code
typedef int my_int;


int main()
//@ requires true;
//@ ensures result == 0;
{   
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;

    // Perform an assertion to check if the arithmetic operation is correct
    assert(t == 8); // VeriFast will attempt to verify this assertion
    return 0;
}

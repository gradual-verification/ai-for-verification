#include <assert.h>

// Define typedef as per original code
typedef int my_int;

/*@ 
  // Specification for main function
  requires true;  // No preconditions
  ensures result == 0;  // The function must return 0
@*/
int main()
{   
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;

    // Perform an assertion to check if the arithmetic operation is correct
    assert(t == 8); // VeriFast will attempt to verify this assertion
    return 0;
}

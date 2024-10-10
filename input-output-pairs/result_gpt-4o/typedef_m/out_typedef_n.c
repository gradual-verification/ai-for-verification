#include <assert.h>
// Verifast requires the <assert.h> header for assertions

typedef int my_int;

/*@ 
  requires true;
  ensures result == 0;
@*/
int main()
{
    // Declare a variable 'x' of type 'my_int' and initialize it to 5
    my_int x = 5;
    
    // Declare a variable 'y' of type 'int' and assign the value of 'x'
    int y = x;
    
    // Declare a variable 'z' of type 'my_int' and assign it the value 3
    my_int z = 3;
    
    // Declare a variable 't' of type 'my_int' and assign it the sum of 'x' and 'z'
    my_int t = x + z;
    
    // Assertion to ensure 't' is equal to 8
    assert(t == 8);
    
    // Return 0
    return 0;
}

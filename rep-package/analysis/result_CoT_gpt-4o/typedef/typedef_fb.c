// Declaration of a typedef for `my_int`
typedef int my_int;

// Main function with Verifast specifications
int main()
    //@ requires true; // No specific input constraints are needed
    /*@
    ensures true; // Execution completes without violating memory safety
                 // or integer bounds (ensures all expressions evaluated correctly).
    @*/
{
    my_int x = 5; // Initializing a my_int (alias for int) to 5
    int y = x;    // Copying value of x to y
    my_int z = 3; // Initializing another my_int to 3
    my_int t = x + z; // Adding x and z and storing the result in t

    // Assertion to ensure the value of t is as expected
    assert(t == 8);

    // Return 0 indicating successful completion
    return 0;
}

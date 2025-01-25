typedef int my_int;

// Main function
int main()
//@ requires true; // No specific input requirements, main is the starting point
//@ ensures true;  // Ensures no specific outcome, just the program terminates without issues
{
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;
    //@ assert t == 8; // An assertion to verify correct computation of t
    return 0;
}

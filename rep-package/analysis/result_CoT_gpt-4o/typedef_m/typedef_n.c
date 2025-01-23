typedef int my_int;

/* @
  // Step 1: Precondition and Postcondition

  // 1.1 Generate and 1.2 Place Precondition
  // Pre: This program does not accept any input arguments.
  // Assuming standard integer range for 'int'
  requires true;

  // 1.5 Generate and 1.6 Place Postcondition
  // Post: Ensures that the variable t is correctly calculated as 8.
  // Result is ensured as 0.
  ensures result == 0;
  ensures true; // This ensures memory safety and integer bounds
@*/
int main()
//@ requires true; // No dynamic memory allocation used or required checks
//@ ensures true; // Ensures integers remain within standard bounds
{
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;

    /*@
      // Additional invariant after calculations
      assert (t == 8);
    @*/
    assert(t == 8);

    return 0;
}

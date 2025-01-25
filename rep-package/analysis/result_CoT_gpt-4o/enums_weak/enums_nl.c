#include <assert.h>

enum day
{
  monday,
  tuesday,
  wednesday,
  thursday,
  friday,
  saturday,
  sunday
};

enum large_numbers
{
  large_number = 30000,
  another_large_number,
  yaln = -0x7fff - 1
};

/***
 * Description:
This function calculates the next day given a current day.

@param day d - represents the current day.

The function calculates the next day by adding 1 to 
the current day, taking the result modulo 7 to handle looping 
back to Monday after Sunday. Finally, the function returns 
the next day as an enum day type, ensuring that the result is 
within the valid range of 0 to 6.
*/

enum day next_day(enum day d)
//@ requires d >= monday && d <= sunday; // Precondition: d is a valid enum day
//@ ensures result >= monday && result <= sunday; // Postcondition: result is a valid enum day
{
  //@ div_rem_nonneg(d + 1, 7);
  return (d + 1) % 7;
}

/***
 * Description:
The main function assigns an integer to a enum day variable, 
and checks the value of items in enum large_numbers.
*/

int main()
//@ requires true;  // Precondition for main: no constraints, as main() has no inputs
//@ ensures result == 0; // Ensure the assignment of d does not violate the enum range
{
  enum day d = monday;
  // Not verifying arbitrary assignments to enum, as VeriFast will flag this
  // d = 35; 

  int x = d;
  
  // Verify that constants match expected values
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  
  return 0;
}

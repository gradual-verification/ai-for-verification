#include <assert.h>
#include <limits.h>

// VeriFast definitions
//@ #include <bitops.gh>

// Enums
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

/*@
predicate valid_day(int d) = 0 <= d && d <= 6;
@*/

/***
 * Description:
 * The next_day function calculates the next day given a current day.
 *
 * @param day d - represents the current day, which is in the range of [0, 6].
 *
 * The function calculates the next day by adding 1 to 
 * the current day, taking the result modulo 7 to handle looping 
 * back to Monday after Sunday. Finally, the function returns 
 * the next day as an enum day type, ensuring that the result is 
 * within the valid range of 0 to 6.
 */
enum day next_day(enum day d)
  //@ requires valid_day(d);
  //@ ensures valid_day(result);
{
  //@ open valid_day(d);
  // No actual loop, just condition checks to validate results
  if (d == sunday) {
    return monday; // Explicit return for clarity
    //@ close valid_day(monday);
  } else {
    return d + 1;
    //@ close valid_day(d + 1);
  }
}

/* @
  // Main does not have specific requirements, assertions ensure logic
  Ensures: true;
@*/

/***
 * Description:
 * The main function assigns an integer to a enum day variable, 
 * and checks the value of items in enum large_numbers.
 */
int main()
  //@ requires true;
  //@ ensures true;
{
  enum day d = monday;
  
  // Trying to assign a value outside the enum's range
  // This demonstrates what happens but would probably be considered invalid usage.
  d = 35; // Note: usually not advised due to out-of-range issues.
  int x = d;

  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}

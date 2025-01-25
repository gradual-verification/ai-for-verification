#include <stdbool.h>

// Declare enum day and its range
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

// Declare enum large_numbers
enum large_numbers
{
  large_number = 30000,
  another_large_number,
  yaln = -0x7fff - 1
};

/*@
  // Predicate to ensure enum day is within valid range
  predicate valid_day(enum day d;) = 0 <= d && d < 7;
  @*/



enum day next_day(enum day d)
//@ requires valid_day(d);
//@ ensures valid_day(result);
{
  // Use lemma to ensure postcondition
  //next_day_ensures_valid(d);
  //@ open valid_day(d);
  //@ div_rem_nonneg(d + 1, 7);
  return (d + 1) % 7;
  //@ close valid_day((d + 1) % 7);
}

int main()
//@ requires true;
//@ ensures true;
{
  enum day d = monday;
  //@ assert valid_day(d);
  
  // Ensure the assignment is valid by restricting to enum range
  d = (35 % 7);
  //@ assert valid_day(d);
  
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  
  return 0;
}

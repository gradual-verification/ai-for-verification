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
  predicate valid_day(enum day d;) =
    d == monday || d == tuesday || d == wednesday ||
    d == thursday || d == friday || d == saturday || d == sunday;
  
  // Lemma ensuring next_day output remains valid
  lemma void next_day_ensures_valid(enum day d)
    requires valid_day(d);
    ensures valid_day((d + 1) % 7);
  {
    // Proof by case analysis
    switch (d) {
      case monday:    break;
      case tuesday:   break;
      case wednesday: break;
      case thursday:  break;
      case friday:    break;
      case saturday:  break;
      case sunday:    break;
    }
  }
  @*/

/*@
  // Specification for next_day function
  requires valid_day(d);
  ensures valid_day(result);
@*/

enum day next_day(enum day d)
{
  // Use lemma to ensure postcondition
  next_day_ensures_valid(d);
  return (d + 1) % 7;
}

int main()
{
  enum day d = monday;
  //@ assert valid_day(d);
  
  // Ensure the assignment is valid by restricting to enum range
  d = (enum day) (35 % 7);
  //@ assert valid_day(d);
  
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  
  return 0;
}

#include <stdbool.h>

enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

// Definitions of verification predicates to capture enum bounds.
//@ predicate valid_day(enum day d) = monday <= d && d <= sunday;

// The next_day function considers a day (represented as an enum) and returns the next day, wrapping around the week.
//@ requires valid_day(d);
//@ ensures valid_day(result);
enum day next_day(enum day d)
{
  return (d + 1) % 7;
}

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

int main()
//@ requires true;
//@ ensures true;
{
  enum day d = monday;
  //@ assert valid_day(d);
  
  d = (enum day)35; // This assignment is erroneous according to the verification logic.
  //@ assert !valid_day(d);           // Verifying that d is outside expected bounds.
  
  int x = d; // Depending on usage, this might not be safe. However, for demonstration of the tool's capabilities:
  //@ assert x == 35;                // Verifying that x was indeed set to the "illegal" value of 35.

  //@ open valid_day(d);           // Open is used to apply or reason with a predicate for a variable.

  // Check the correctness of the large number enums.
  assert(large_number == 30000); 
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);

  //@ close valid_day(d); // Fix: If using predicates, close any open predicates affecting the memory location.
  
  return 0;
}

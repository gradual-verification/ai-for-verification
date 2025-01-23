enum day { monday = 0, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1 };

// Function to get the next day of the week
enum day next_day(enum day d)
//@ requires d >= monday && d <= sunday;
//@ ensures result >= monday && result <= sunday &*& result == ((d == sunday) ? monday : d + 1);
{
  if (d == 6) {
    //@ div_rem_nonneg_unique(d + 1, 7, 1, 0);
  } else {
    //@ div_rem_nonneg_unique(d + 1, 7, 0, d + 1);
  }
  return (d + 1) % 7;
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  enum day d = monday;
  //@ assert d >= monday && d <= sunday;  // Ensure value of d is within the range
  int x = next_day(d);                   // Get the next day
  assert(x >= monday && x <= sunday);    // Verify the result is within enum day range
  d = 35;                                // Violation example - this goes out of bounds of enum
  //@ assert d == 35;                     // The code doesn't check validity of enum here
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
